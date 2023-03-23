//! A crate for handling [URNs](https://datatracker.ietf.org/doc/html/rfc8141).
//!
//! Features
//! - `serde` - [Serde](https://serde.rs) support
//! - `std` (enabled by default) - [`std::error::Error`] integration
//!
//! # Example
//! ```
//! # #[cfg(not(feature = "std"))]
//! # fn main() { }
//! # #[cfg(feature = "std")]
//! # use urn::{Urn, UrnBuilder};
//! # #[cfg(feature = "std")]
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! let urn = UrnBuilder::new("example", "1234:5678").build()?;
//! assert_eq!(urn.as_str(), "urn:example:1234:5678");
//! assert_eq!(urn, "urn:example:1234:5678".parse()?); // Using std::str::parse
//! assert_eq!(urn.nss(), "1234:5678");
//! # Ok(())
//! # }
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::{
    borrow::{Cow, ToOwned},
    fmt,
    string::String,
};
use core::{
    convert::{TryFrom, TryInto},
    hash::{self, Hash},
    num::{NonZeroU32, NonZeroU8},
    ops::{Deref, Range},
    slice::SliceIndex,
};
#[cfg(feature = "alloc")]
use core::str::FromStr;
#[cfg(feature = "std")]
use std::{borrow::Cow, fmt};

#[cfg(not(feature = "alloc"))]
type Cow<'a, T> = &'a T;

#[cfg(feature = "alloc")]
fn cow_mut_ref<'a>(c: &'a mut Cow<str>, alloc_allowed: bool) -> Result<&'a mut str> {
    if let Cow::Borrowed(s) = c {
        if alloc_allowed {
            *c = s.to_owned().into();
        } else {
            return Err(Error::AllocRequired)
        }
    }
    if let Cow::Owned(s) = c {
        Ok(s.as_mut_str())
    } else {
        unreachable!("cow isn't owned after making it owned, what happened?")
    }
}

#[cfg(not(feature = "alloc"))]
fn cow_mut_ref<'a>(_: &'a mut Cow<str>, _alloc_allowed: bool) -> Result<&'a mut str> {
    Err(Error::AllocRequired)
}

fn make_uppercase<R>(c: &mut Cow<str>, range: R, alloc_allowed: bool) -> Result<()>
where
    R: Clone + SliceIndex<str, Output = str>,
{
    if c[range.clone()].bytes().any(|b| b.is_ascii_lowercase()) {
        cow_mut_ref(c, alloc_allowed)?[range].make_ascii_uppercase();
    }
    Ok(())
}

fn make_lowercase<R>(c: &mut Cow<str>, range: R, alloc_allowed: bool) -> Result<()>
where
    R: Clone + SliceIndex<str, Output = str>,
{
    if c[range.clone()].bytes().any(|b| b.is_ascii_uppercase()) {
        cow_mut_ref(c, alloc_allowed)?[range].make_ascii_lowercase();
    }
    Ok(())
}

/// Checks whether a string is a valid NID
fn is_valid_nid(s: &str) -> bool {
    // RFC8141:
    // NID = (alphanum) 0*30(ldh) (alphanum)
    // ldh = alphanum / "-"
    //
    // RFC2141 additionally allows NIDs to end with -
    (2..=32).contains(&s.len())
        && !s.starts_with('-')
        && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

/// Different components are percent-encoded differently...
#[derive(Copy, Clone)]
enum PctEncoded {
    Nss,
    RComponent,
    QComponent,
    FComponent,
}

/// Parse percent-encoded string. Returns the end.
fn parse_pct_encoded(s: &mut Cow<str>, start: usize, kind: PctEncoded, alloc_allowed: bool) -> Result<usize> {
    let mut it = s.bytes().enumerate().skip(start).peekable();
    while let Some((i, ch)) = it.next() {
        // unwrap: i is always less than to s.len(), s' length isn't changed in the loop
        match (kind, ch) {
            /* question mark handling */
            // ? is always allowed in f-components
            (PctEncoded::FComponent, b'?') => {}
            // ? is a valid part of q-component if not at the start
            (PctEncoded::QComponent, b'?') if i != start => {}
            // ? is a valid part of r-component if not at the start, but ?= indicates the q-component start, so only allow the ? if it isn't followed by =
            (PctEncoded::RComponent, b'?') if i != start && it.peek().map(|x| x.1) != Some(b'=') => {}
            /* slash handling */
            // slash is uniquely allowed at the start of f-component...
            (PctEncoded::FComponent, b'/') => {}
            // ...but it's allowed everywhere if it isn't at the start
            (_, b'/') if i != start => {}
            /* the rest is handled the same everywhere */
            // various symbols that are allowed as pchar
            (
                _,
                // unreserved = ALPHA / DIGIT / <the following symbols>
                b'-' | b'.' | b'_' | b'~'
                // sub-delims = <the following symbols>
                | b'!' | b'$' | b'&' | b'\'' | b'(' | b')' | b'*' | b'+' | b',' | b';' | b'='
                // pchar = unreserved / pct-encoded / sub-delims / <the following symbols>
                | b':' | b'@',
            ) => {}
            // pct-encoded = "%" HEXDIG HEXDIG
            // HEXDIG =  DIGIT / "A" / "B" / "C" / "D" / "E" / "F"
            // (ABNF strings are case insensitive)
            (_, b'%') => {
                let mut pct_chars = it.take(2);
                if pct_chars.len() == 2 && pct_chars.all(|x| x.1.is_ascii_hexdigit()) {
                    // percent encoding must be normalized by uppercasing it
                    make_uppercase(s, i + 1..i + 3, alloc_allowed)?;
                    it = s.bytes().enumerate().skip(i + 3).peekable();
                } else {
                    return Ok(i)
                }
            }
            // ALPHA / DIGIT
            (_, c) if c.is_ascii_alphanumeric() => {}
            // other characters can't be part of this component, so this is the end
            _ => return Ok(i),
        }
    }
    // this was the last component!
    Ok(s.len())
}

/// Returns the NSS end
fn parse_nss(s: &mut Cow<str>, start: usize, alloc_allowed: bool) -> Result<usize> {
    parse_pct_encoded(s, start, PctEncoded::Nss, alloc_allowed)
}

/// Returns the r-component end
fn parse_r_component(s: &mut Cow<str>, start: usize, alloc_allowed: bool) -> Result<usize> {
    parse_pct_encoded(s, start, PctEncoded::RComponent, alloc_allowed)
}

/// Returns the q-component end
fn parse_q_component(s: &mut Cow<str>, start: usize, alloc_allowed: bool) -> Result<usize> {
    parse_pct_encoded(s, start, PctEncoded::QComponent, alloc_allowed)
}

/// Returns the f-component end
fn parse_f_component(s: &mut Cow<str>, start: usize, alloc_allowed: bool) -> Result<usize> {
    parse_pct_encoded(s, start, PctEncoded::FComponent, alloc_allowed)
}

const URN_PREFIX: &str = "urn:";
const NID_NSS_SEPARATOR: &str = ":";
const RCOMP_PREFIX: &str = "?+";
const QCOMP_PREFIX: &str = "?=";
const FCOMP_PREFIX: &str = "#";

fn parse_urn(mut s: Cow<str>, alloc_allowed: bool) -> Result<Urn> {
    // ensure that the first 4 bytes are a valid substring
    if !s.is_char_boundary(URN_PREFIX.len()) {
        return Err(Error::InvalidScheme);
    }

    make_lowercase(&mut s, ..URN_PREFIX.len(), alloc_allowed)?;

    if &s[..URN_PREFIX.len()] != URN_PREFIX {
        return Err(Error::InvalidScheme);
    }

    let nid_start = URN_PREFIX.len();
    let nid_end = nid_start
        + s[nid_start..].find(NID_NSS_SEPARATOR).ok_or_else(|| {
            if is_valid_nid(&s[nid_start..]) {
                // If NID is present, but the NSS and its separator aren't, it counts as an NSS error
                Error::InvalidNss
            } else {
                // the NSS separator couldn't be found, but whatever has been found doesn't even count as a valid NID
                Error::InvalidNid
            }
        })?;

    if !is_valid_nid(&s[nid_start..nid_end]) {
        return Err(Error::InvalidNid);
    }

    // Now that we know the NID is valid, normalize it
    make_lowercase(&mut s, nid_start..nid_end, alloc_allowed)?;

    let nss_start = nid_end + NID_NSS_SEPARATOR.len();
    let nss_end = parse_nss(&mut s, nss_start, alloc_allowed)?;

    // NSS must be at least one character long
    if nss_end == nss_start {
        return Err(Error::InvalidNss);
    }

    let mut end = nss_end;
    let mut last_component_error = Error::InvalidNss;

    let r_component_len = if s[end..].starts_with(RCOMP_PREFIX) {
        let rc_start = end + RCOMP_PREFIX.len();
        end = parse_r_component(&mut s, rc_start, alloc_allowed)?;
        last_component_error = Error::InvalidRComponent;
        Some(
            (end - rc_start)
                .try_into()
                .ok()
                .and_then(NonZeroU32::new)
                .ok_or(last_component_error)?,
        )
    } else {
        None
    };

    let q_component_len = if s[end..].starts_with(QCOMP_PREFIX) {
        let qc_start = end + QCOMP_PREFIX.len();
        end = parse_q_component(&mut s, qc_start, alloc_allowed)?;
        last_component_error = Error::InvalidQComponent;
        Some(
            (end - qc_start)
                .try_into()
                .ok()
                .and_then(NonZeroU32::new)
                .ok_or(last_component_error)?,
        )
    } else {
        None
    };

    if s[end..].starts_with(FCOMP_PREFIX) {
        let fc_start = end + FCOMP_PREFIX.len();
        end = parse_f_component(&mut s, fc_start, alloc_allowed)?;
        last_component_error = Error::InvalidFComponent;
    }

    if end < s.len() {
        return Err(last_component_error);
    }

    Ok(Urn {
        #[cfg(feature = "alloc")]
        alloc_allowed,
        urn: s,
        // unwrap: NID length range is 2..=32 bytes, so it always fits into non-zero u8
        nid_len: NonZeroU8::new((nid_end - nid_start).try_into().unwrap()).unwrap(),
        // unwrap: NSS always has non-zero length
        nss_len: NonZeroU32::new(
            (nss_end - nss_start)
                .try_into()
                .map_err(|_| Error::InvalidNss)?,
        )
        .unwrap(),
        r_component_len,
        q_component_len,
    })
}

/// A URN validation error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The URN has an invalid scheme.
    InvalidScheme,
    /// The URN has an invalid NID (Namespace ID).
    InvalidNid,
    /// The URN has an invalid NSS (Namespace-specific string).
    InvalidNss,
    /// The URN has an invalid r-component.
    InvalidRComponent,
    /// The URN has an invalid q-component.
    InvalidQComponent,
    /// The URN has an invalid f-component.
    InvalidFComponent,
    /// Allocation is required, but not possible
    AllocRequired,
}

#[cfg(feature = "alloc")]
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidScheme => "invalid urn scheme",
            Self::InvalidNid => "invalid urn nid (namespace id)",
            Self::InvalidNss => "invalid urn nss (namespace-specific string)",
            Self::InvalidRComponent => "invalid urn r-component",
            Self::InvalidQComponent => "invalid urn q-component",
            Self::InvalidFComponent => "invalid urn f-component (fragment)",
            Self::AllocRequired => "an allocation was required, but not possible",
        })
    }
}

type Result<T, E = Error> = core::result::Result<T, E>;

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// An RFC2141/8141 URN (Uniform Resource Name).
///
/// **Note:** the equivalence checks are done
/// [according to the specification](https://www.rfc-editor.org/rfc/rfc8141.html#section-3),
/// only taking the NID and NSS into account! If you need exact equivalence checks, consider
/// comparing using `Urn::as_str()` as the key. Some namespaces may define additional lexical
/// equivalence rules, these aren't accounted for in this implementation (Meaning there might be
/// false negatives for some namespaces). There will, however, be no false positives.
#[derive(Clone, Debug)]
pub struct Urn<'a> {
    // Entire URN string
    urn: Cow<'a, str>,
    nid_len: NonZeroU8,
    nss_len: NonZeroU32,
    r_component_len: Option<NonZeroU32>,
    q_component_len: Option<NonZeroU32>,
    #[cfg(feature = "alloc")]
    alloc_allowed: bool,
}

impl<'a> Urn<'a> {
    const fn nid_range(&self) -> Range<usize> {
        // urn:<nid>
        let start = URN_PREFIX.len();
        start..start + self.nid_len.get() as usize
    }

    const fn nss_range(&self) -> Range<usize> {
        // ...<nid>:<nss>
        let start = self.nid_range().end + NID_NSS_SEPARATOR.len();
        start..start + self.nss_len.get() as usize
    }

    fn r_component_range(&self) -> Option<Range<usize>> {
        self.r_component_len.map(|r_component_len| {
            // ...<nss>[?+<r-component>]
            let start = self.nss_range().end + RCOMP_PREFIX.len();
            start..start + r_component_len.get() as usize
        })
    }

    /// end of the last component before q-component
    fn pre_q_component_end(&self) -> usize {
        self.r_component_range()
            .unwrap_or_else(|| self.nss_range())
            .end
    }

    fn q_component_range(&self) -> Option<Range<usize>> {
        self.q_component_len.map(|q_component_len| {
            // ...<nss>[?+<r-component>][?=<q-component>]
            let start = self.pre_q_component_end() + QCOMP_PREFIX.len();
            start..start + q_component_len.get() as usize
        })
    }

    /// end of the last component before f-component
    fn pre_f_component_end(&self) -> usize {
        self.q_component_range()
            .or_else(|| self.r_component_range())
            .unwrap_or_else(|| self.nss_range())
            .end
    }

    fn f_component_start(&self) -> Option<usize> {
        // ...[#<f-component>]
        Some(self.pre_f_component_end())
            .filter(|x| *x < self.urn.len())
            .map(|x| x + FCOMP_PREFIX.len())
    }

    /// String representation of this URN (Canonicized).
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.urn
    }

    /// NID (Namespace identifier), the first part of the URN.
    ///
    /// For example, in `urn:ietf:rfc:2648`, `ietf` is the namespace.
    #[must_use]
    pub fn nid(&self) -> &str {
        &self.urn[self.nid_range()]
    }
    /// Set the NID (must be [a valid NID](https://datatracker.ietf.org/doc/html/rfc8141#section-2)).
    /// # Errors
    /// Returns [`Error::InvalidNid`] in case of a validation failure.
    #[cfg(feature = "alloc")]
    pub fn set_nid(&mut self, nid: &str) -> Result<()> {
        if !is_valid_nid(nid) {
            return Err(Error::InvalidNid);
        }
        let mut nid = Cow::from(nid);
        make_lowercase(&mut nid, .., self.alloc_allowed)?;
        let range = self.nid_range();
        self.urn.to_mut().replace_range(range, &nid);
        // unwrap: NID length range is 2..=32 bytes, so it always fits into non-zero u8
        self.nid_len = NonZeroU8::new(nid.len().try_into().unwrap()).unwrap();
        Ok(())
    }
    /// NSS (Namespace-specific string) identifying the resource.
    ///
    /// For example, in `urn:ietf:rfc:2648`, `rfs:2648` is the NSS.
    #[must_use]
    pub fn nss(&self) -> &str {
        &self.urn[self.nss_range()]
    }
    /// Set the NSS (must be [a valid NSS](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidNss`] in case of a validation failure.
    #[cfg(feature = "alloc")]
    pub fn set_nss(&mut self, nss: &str) -> Result<()> {
        let mut nss = Cow::from(nss);
        if nss.is_empty() || parse_nss(&mut nss, 0, self.alloc_allowed)? != nss.len() {
            return Err(Error::InvalidNss);
        }
        // unwrap: NSS length is non-zero as checked above
        let nss_len =
            NonZeroU32::new(nss.len().try_into().map_err(|_| Error::InvalidNss)?).unwrap();
        let range = self.nss_range();
        self.urn.to_mut().replace_range(range, &nss);
        self.nss_len = nss_len;
        Ok(())
    }
    /// r-component, following the `?+` character sequence, to be used for passing parameters
    /// to URN resolution services.
    ///
    /// In `urn:example:foo-bar-baz-qux?+CCResolve:cc=uk`, the r-component is `CCResolve:cc=uk`.
    ///
    /// Should not be used for equivalence checks. As of the time of writing this, exact semantics are undefined.
    #[must_use]
    pub fn r_component(&self) -> Option<&str> {
        self.r_component_range().map(|range| &self.urn[range])
    }
    /// Set the r-component (must be [a valid r-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidRComponent`] in case of a validation failure.
    #[cfg(feature = "alloc")]
    pub fn set_r_component(&mut self, r_component: Option<&str>) -> Result<()> {
        if let Some(rc) = r_component {
            let mut rc = Cow::from(rc);
            if rc.is_empty() || parse_r_component(&mut rc, 0, self.alloc_allowed)? != rc.len() {
                return Err(Error::InvalidRComponent);
            }
            let rc_len = rc.len().try_into().map_err(|_| Error::InvalidRComponent)?;
            // insert RCOMP_PREFIX if r-component doesn't already exist
            let range = self.r_component_range().unwrap_or_else(|| {
                let nss_end = self.nss_range().end;
                self.urn.to_mut().replace_range(nss_end..nss_end, RCOMP_PREFIX);
                nss_end + RCOMP_PREFIX.len()..nss_end + RCOMP_PREFIX.len()
            });
            self.urn.to_mut().replace_range(range, &rc);
            self.r_component_len = Some(NonZeroU32::new(rc_len).unwrap());
        } else if let Some(mut range) = self.r_component_range() {
            range.start -= RCOMP_PREFIX.len();
            self.urn.to_mut().replace_range(range, "");
            self.r_component_len = None;
        }
        Ok(())
    }
    /// q-component, following the `?=` character sequence. Has a similar function to the URL query
    /// string.
    ///
    /// In `urn:example:weather?=op=map&lat=39.56&lon=-104.85`,
    /// the q-component is `op=map&lat=39.56&lon=-104.85`.
    ///
    /// Should not be used for equivalence checks.
    #[must_use]
    pub fn q_component(&self) -> Option<&str> {
        self.q_component_range().map(|range| &self.urn[range])
    }
    /// Set the q-component (must be [a valid q-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidQComponent`] in case of a validation failure.
    #[cfg(feature = "alloc")]
    pub fn set_q_component(&mut self, q_component: Option<&str>) -> Result<()> {
        if let Some(qc) = q_component {
            let mut qc = Cow::from(qc);
            if qc.is_empty() || parse_q_component(&mut qc, 0, self.alloc_allowed)? != qc.len() {
                return Err(Error::InvalidQComponent);
            }
            let qc_len = qc.len().try_into().map_err(|_| Error::InvalidQComponent)?;
            // insert QCOMP_PREFIX if q-component doesn't already exist
            let range = self.q_component_range().unwrap_or_else(|| {
                let pre_qc_end = self.pre_q_component_end();
                self.urn.to_mut().replace_range(pre_qc_end..pre_qc_end, QCOMP_PREFIX);
                pre_qc_end + QCOMP_PREFIX.len()..pre_qc_end + QCOMP_PREFIX.len()
            });
            self.urn.to_mut().replace_range(range, &qc);
            self.q_component_len = Some(NonZeroU32::new(qc_len).unwrap());
        } else if let Some(mut range) = self.q_component_range() {
            range.start -= QCOMP_PREFIX.len();
            self.urn.to_mut().replace_range(range, "");
            self.q_component_len = None;
        }
        Ok(())
    }
    /// f-component following the `#` character at the end of the URN. Has a similar function to
    /// the URL fragment.
    ///
    /// In `urn:example:a123,z456#789`, the f-component is `789`.
    ///
    /// Should not be used for equivalence checks.
    #[must_use]
    pub fn f_component(&self) -> Option<&str> {
        self.f_component_start().map(|start| &self.urn[start..])
    }
    /// Set the f-component (must be [a valid f-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidFComponent`] in case of a validation failure.
    #[cfg(feature = "alloc")]
    pub fn set_f_component(&mut self, f_component: Option<&str>) -> Result<()> {
        if let Some(fc) = f_component {
            let mut fc = Cow::from(fc);
            if parse_f_component(&mut fc, 0, self.alloc_allowed)? != fc.len() {
                return Err(Error::InvalidFComponent);
            }
            let start = self.f_component_start().unwrap_or_else(|| {
                let range = self.urn.len()..self.urn.len();
                self.urn.to_mut().replace_range(range, FCOMP_PREFIX);
                self.urn.len()
            });
            self.urn.to_mut().replace_range(start.., &fc);
        } else if let Some(start) = self.f_component_start() {
            self.urn.to_mut().replace_range(start - FCOMP_PREFIX.len().., "");
        }
        Ok(())
    }
}

impl Deref for Urn<'_> {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        &self.urn
    }
}

impl AsRef<[u8]> for Urn<'_> {
    fn as_ref(&self) -> &[u8] {
        self.urn.as_bytes()
    }
}

impl AsRef<str> for Urn<'_> {
    fn as_ref(&self) -> &str {
        &self.urn
    }
}

impl PartialEq for Urn<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.urn[..self.nss_range().end] == other.urn[..other.nss_range().end]
    }
}

impl Eq for Urn<'_> {}

impl Hash for Urn<'_> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.urn[..self.nss_range().end].hash(state);
    }
}

#[cfg(feature = "alloc")]
impl fmt::Display for Urn<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(&self.urn)
    }
}

#[cfg(feature = "alloc")]
impl FromStr for Urn<'_> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        parse_urn(s.to_owned().into(), true)
    }
}

impl<'a> TryFrom<&'a str> for Urn<'a> {
    type Error = Error;
    fn try_from(value: &'a str) -> Result<Self> {
        parse_urn(value.into(), true)
    }
}

#[cfg(feature = "alloc")]
impl TryFrom<String> for Urn<'static> {
    type Error = Error;
    fn try_from(value: String) -> Result<Self> {
        parse_urn(value.into(), true)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> serde::Deserialize<'de> for Urn<'static> {
    fn deserialize<D>(de: D) -> Result<Self, <D as serde::Deserializer<'de>>::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Urn::try_from(String::deserialize(de)?).map_err(serde::de::Error::custom)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl serde::Serialize for Urn<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self)
    }
}

/// A struct used for constructing URNs.
///
/// # Example
/// ```
/// # #[cfg(not(feature = "std"))]
/// # fn main() { }
/// # #[cfg(feature = "std")]
/// # use urn::{Urn, UrnBuilder};
/// # #[cfg(feature = "std")]
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// let urn = UrnBuilder::new("example", "1234:5678").build()?;
/// assert_eq!(urn.as_str(), "urn:example:1234:5678");
/// assert_eq!(urn, "urn:example:1234:5678".parse()?); // Using std::str::parse
/// assert_eq!(urn.nss(), "1234:5678");
/// # Ok(())
/// # }
/// ```
#[cfg(feature = "alloc")]
#[derive(Debug)]
#[must_use]
pub struct UrnBuilder<'a> {
    nid: &'a str,
    nss: &'a str,
    r_component: Option<&'a str>,
    q_component: Option<&'a str>,
    f_component: Option<&'a str>,
}

#[cfg(feature = "alloc")]
impl<'a> UrnBuilder<'a> {
    /// Create a new `UrnBuilder`.
    pub fn new(nid: &'a str, nss: &'a str) -> Self {
        Self {
            nid,
            nss,
            r_component: None,
            q_component: None,
            f_component: None,
        }
    }
    /// Change the namespace id.
    pub fn nid(mut self, nid: &'a str) -> Self {
        self.nid = nid;
        self
    }
    /// Change the namespace-specific string (must be percent encoded as per RFC).
    pub fn nss(mut self, nss: &'a str) -> Self {
        self.nss = nss;
        self
    }
    /// Change the r-component (must be percent encoded as per RFC).
    pub fn r_component(mut self, r_component: Option<&'a str>) -> Self {
        self.r_component = r_component;
        self
    }
    /// Change the q-component (must be percent encoded as per RFC).
    pub fn q_component(mut self, q_component: Option<&'a str>) -> Self {
        self.q_component = q_component;
        self
    }
    /// Change the f-component (must be percent encoded as per RFC).
    pub fn f_component(mut self, f_component: Option<&'a str>) -> Self {
        self.f_component = f_component;
        self
    }
    /// [Validate the data](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and create the URN.
    ///
    /// # Errors
    ///
    /// In case of a validation failure, returns an error specifying the component that failed
    /// validation
    pub fn build(self) -> Result<Urn<'static>> {
        fn cow_push_str(c: &mut Cow<str>, s: &str) {
            if let Cow::Owned(c) = c {
                c.push_str(s);
            } else {
                unreachable!("cow must be owned to use this function")
            }
        }
        if !is_valid_nid(self.nid) {
            return Err(Error::InvalidNid);
        }
        let mut s = Cow::from(URN_PREFIX.to_owned());
        {
            let s = &mut s;
            cow_push_str(s, self.nid);
            cow_push_str(s, NID_NSS_SEPARATOR);
            let nss_start = s.len();
            cow_push_str(s, self.nss);
            if self.nss.is_empty() || parse_nss(s, nss_start, true)? != s.len() {
                return Err(Error::InvalidNss);
            }
            if let Some(rc) = self.r_component {
                cow_push_str(s, RCOMP_PREFIX);
                let rc_start = s.len();
                cow_push_str(s, rc);
                if rc.is_empty() || parse_r_component(s, rc_start, true)? != s.len() {
                    return Err(Error::InvalidRComponent);
                }
            }
            if let Some(qc) = self.q_component {
                cow_push_str(s, QCOMP_PREFIX);
                let qc_start = s.len();
                cow_push_str(s, qc);
                if qc.is_empty() || parse_q_component(s, qc_start, true)? != s.len() {
                    return Err(Error::InvalidQComponent);
                }
            }
            if let Some(fc) = self.f_component {
                cow_push_str(s, FCOMP_PREFIX);
                let fc_start = s.len();
                cow_push_str(s, fc);
                if parse_f_component(s, fc_start, true)? != s.len() {
                    return Err(Error::InvalidFComponent);
                }
            }
        }
        Ok(Urn {
            // we already had to allocate since we use a builder, obviously allocations are allowed
            alloc_allowed: true,
            urn: s,
            // unwrap: NID length range is 2..=32 bytes, so it always fits into non-zero u8
            nid_len: NonZeroU8::new(self.nid.len().try_into().unwrap()).unwrap(),
            // unwrap: NSS length is non-zero as checked above
            nss_len: NonZeroU32::new(self.nss.len().try_into().map_err(|_| Error::InvalidNss)?)
                .unwrap(),
            r_component_len: self
                .r_component
                .map(|x| {
                    x.len()
                        .try_into()
                        // unwrap: r-component has non-zero length as checked above
                        .map(|x| NonZeroU32::new(x).unwrap())
                        .map_err(|_| Error::InvalidRComponent)
                })
                .transpose()?,
            q_component_len: self
                .q_component
                .map(|x| {
                    x.len()
                        .try_into()
                        // unwrap: q-component has non-zero length as checked above
                        .map(|x| NonZeroU32::new(x).unwrap())
                        .map_err(|_| Error::InvalidQComponent)
                })
                .transpose()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(feature = "std"))]
    use super::alloc::string::ToString;

    #[test]
    fn it_works() {
        Urn::try_from("6򭞦*�").unwrap_err();
        #[cfg(feature = "alloc")]
        assert_eq!(
            Urn::try_from("urn:nbn:de:bvb:19-146642").unwrap(),
            UrnBuilder::new("nbn", "de:bvb:19-146642").build().unwrap()
        );
        assert_eq!(
            Urn::try_from("urn:nbn:de:bvb:19-146642")
                .unwrap()
                .to_string(),
            "urn:nbn:de:bvb:19-146642"
        );

        #[cfg(feature = "alloc")]
        assert_eq!(
            Urn::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test")
                .unwrap(),
            UrnBuilder::new("example", "foo-bar-baz-qux")
                .r_component(Some("CCResolve:cc=uk"))
                .f_component(Some("test"))
                .build()
                .unwrap()
        );
        assert_eq!(
            Urn::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test")
                .unwrap()
                .f_component()
                .unwrap(),
            "test"
        );
        assert_eq!(
            Urn::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test")
                .unwrap()
                .r_component()
                .unwrap(),
            "CCResolve:cc=uk"
        );
        assert_eq!(
            Urn::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test")
                .unwrap()
                .to_string(),
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test",
        );

        #[cfg(feature = "alloc")]
        assert_eq!(
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
                .parse::<Urn>()
                .unwrap(),
            UrnBuilder::new("example", "weather")
                .q_component(Some(
                    "op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
                ))
                .build()
                .unwrap()
        );
        assert_eq!(
            Urn::try_from("urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z")
                .unwrap()
                .to_string(),
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
        );

        #[cfg(feature = "alloc")]
        assert_eq!(
            "uRn:eXaMpLe:%3d%3a?=aoiwnfuafo".parse::<Urn>().unwrap(),
            UrnBuilder::new("example", "%3D%3a").build().unwrap()
        );
        #[cfg(feature = "alloc")]
        assert_eq!(
            "uRn:eXaMpLe:%3d%3a?=aoiwnfuafo"
                .parse::<Urn>()
                .unwrap()
                .to_string(),
            "urn:example:%3D%3A?=aoiwnfuafo",
        );

        assert_eq!(Urn::try_from("urn:-example:abcd"), Err(Error::InvalidNid));
        assert_eq!(Urn::try_from("urn:example:/abcd"), Err(Error::InvalidNss));
        assert_eq!(Urn::try_from("urn:a:abcd"), Err(Error::InvalidNid));
        assert_eq!(
            Urn::try_from("urn:0123456789abcdef0123456789abcdef0:abcd"),
            Err(Error::InvalidNid)
        );
        let _ = Urn::try_from("urn:0123456789abcdef0123456789abcdef:abcd")
            .unwrap();
        assert_eq!(Urn::try_from("urn:example"), Err(Error::InvalidNss));
        assert_eq!(Urn::try_from("urn:example:"), Err(Error::InvalidNss));
        assert_eq!(Urn::try_from("urn:example:%"), Err(Error::InvalidNss));
        assert_eq!(Urn::try_from("urn:example:%a"), Err(Error::InvalidNss));
        assert_eq!(Urn::try_from("urn:example:%a_"), Err(Error::InvalidNss));
        #[cfg(feature = "alloc")]
        assert_eq!(
            Urn::try_from("urn:example:%a0?+"),
            Err(Error::InvalidRComponent)
        );
        #[cfg(feature = "alloc")]
        assert_eq!(
            Urn::try_from("urn:example:%a0?+%a0?="),
            Err(Error::InvalidQComponent)
        );
        #[cfg(feature = "alloc")]
        assert_eq!(
            Urn::try_from("urn:example:%a0?+%a0?=a")
                .unwrap()
                .r_component()
                .unwrap(),
            "%A0",
        );

        #[cfg(feature = "alloc")]
        {
            let mut urn = "urn:example:test".parse::<Urn>().unwrap();
            urn.set_f_component(Some("f-component")).unwrap();
            assert_eq!(urn.f_component(), Some("f-component"));
            assert_eq!(urn.as_str(), "urn:example:test#f-component");
            urn.set_f_component(Some("")).unwrap();
            assert_eq!(urn.f_component(), Some(""));
            assert_eq!(urn.as_str(), "urn:example:test#");
            urn.set_q_component(Some("abcd")).unwrap();
            assert_eq!(urn.q_component(), Some("abcd"));
            assert_eq!(urn.as_str(), "urn:example:test?=abcd#");
            assert!(urn.set_q_component(Some("")).is_err());
            urn.set_r_component(Some("%2a")).unwrap();
            assert_eq!(urn.r_component(), Some("%2A"));
            assert_eq!(urn.as_str(), "urn:example:test?+%2A?=abcd#");
            urn.set_nid("a-b").unwrap();
            assert_eq!(urn.as_str(), "urn:a-b:test?+%2A?=abcd#");
            urn.set_r_component(None).unwrap();
            assert_eq!(urn.as_str(), "urn:a-b:test?=abcd#");
            assert_eq!(urn.r_component(), None);
        }
    }
}
