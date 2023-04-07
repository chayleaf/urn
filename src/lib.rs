//! A crate for handling [URNs](https://datatracker.ietf.org/doc/html/rfc8141).
//!
//! Features
//! - `serde` - [Serde](https://serde.rs) support
//! - `std` (enabled by default) - [`std::error::Error`] integration
//! - `alloc` (enabled by default) - [`alloc`] support (you probably want to keep this enabled)
//! - `nightly` - use `core::error::Error` rather than `std::error::Error`. **Warning: this feature
//!   might be removed later and it won't be considered a breaking change!**
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
#![allow(clippy::missing_panics_doc)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(feature = "nightly", feature(error_in_core))]
#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::{borrow::ToOwned, string::String};
#[cfg(feature = "alloc")]
use core::str::FromStr;
use core::{
    convert::{TryFrom, TryInto},
    fmt,
    hash::{self, Hash},
    num::{NonZeroU32, NonZeroU8},
    ops::Range,
};

#[cfg(feature = "std")]
use std::error;
#[cfg(all(not(feature = "std"), feature = "nightly"))]
use core::error;

mod cow;
use cow::{make_lowercase, make_uppercase, replace_range, TriCow};

#[cfg(feature = "alloc")]
mod owned;
#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub use owned::Urn;

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub mod percent;
#[cfg(not(feature = "alloc"))]
mod percent;
use percent::{parse_nss, parse_r_component, parse_q_component, parse_f_component};

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

const URN_PREFIX: &str = "urn:";
const NID_NSS_SEPARATOR: &str = ":";
const RCOMP_PREFIX: &str = "?+";
const QCOMP_PREFIX: &str = "?=";
const FCOMP_PREFIX: &str = "#";

fn parse_urn(mut s: TriCow) -> Result<UrnSlice> {
    // ensure that the first 4 bytes are a valid substring
    if !s.is_char_boundary(URN_PREFIX.len()) {
        return Err(Error::InvalidScheme);
    }

    make_lowercase(&mut s, ..URN_PREFIX.len())?;

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
    make_lowercase(&mut s, nid_start..nid_end)?;

    let nss_start = nid_end + NID_NSS_SEPARATOR.len();
    let nss_end = parse_nss(&mut s, nss_start)?;

    // NSS must be at least one character long
    if nss_end == nss_start {
        return Err(Error::InvalidNss);
    }

    let mut end = nss_end;
    let mut last_component_error = Error::InvalidNss;

    let r_component_len = if s[end..].starts_with(RCOMP_PREFIX) {
        let rc_start = end + RCOMP_PREFIX.len();
        end = parse_r_component(&mut s, rc_start)?;
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
        end = parse_q_component(&mut s, qc_start)?;
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
        end = parse_f_component(&mut s, fc_start)?;
        last_component_error = Error::InvalidFComponent;
    }

    if end < s.len() {
        return Err(last_component_error);
    }

    Ok(UrnSlice {
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

#[cfg(any(feature = "std", feature = "nightly"))]
impl error::Error for Error {}

/// A borrowed RFC2141/8141 URN (Uniform Resource Name).
///
/// **Note:** the equivalence checks are done
/// [according to the specification](https://www.rfc-editor.org/rfc/rfc8141.html#section-3),
/// only taking the NID and NSS into account! If you need exact equivalence checks, consider
/// comparing using `Urn::as_str()` as the key. Some namespaces may define additional lexical
/// equivalence rules, these aren't accounted for in this implementation (Meaning there might be
/// false negatives for some namespaces). There will, however, be no false positives.
///
/// Unlike [`Urn`]:
/// - When created via `TryFrom<&str>`, allocations only occur if the URN isn't normalized
///   (uppercase percent-encoded characters and lowercase `urn` scheme and NID)
/// - When created via `TryFrom<&mut str>`, no allocations are done at all (however, if you
///   explicitly disable the `alloc` feature, attempts to to clone the `UrnSlice` created this way
///   will panic).
///
/// `FromStr` is always required to allocate, so you should use `TryFrom` when possible.
#[derive(Clone, Debug)]
pub struct UrnSlice<'a> {
    // Entire URN string
    urn: TriCow<'a>,
    nid_len: NonZeroU8,
    nss_len: NonZeroU32,
    r_component_len: Option<NonZeroU32>,
    q_component_len: Option<NonZeroU32>,
}

impl<'a> UrnSlice<'a> {
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

    /// String representation of this URN (Normalized).
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
    /// Set the NID (must be [a valid
    /// NID](https://datatracker.ietf.org/doc/html/rfc8141#section-2)).
    ///
    /// # Errors
    /// Returns [`Error::InvalidNid`] in case of a validation failure.
    pub fn set_nid(&mut self, nid: &str) -> Result<()> {
        if !is_valid_nid(nid) {
            return Err(Error::InvalidNid);
        }
        let mut nid = TriCow::Borrowed(nid);
        make_lowercase(&mut nid, ..)?;
        let range = self.nid_range();
        replace_range(&mut self.urn, range, &nid)?;
        // unwrap: NID length range is 2..=32 bytes, so it always fits into non-zero u8
        self.nid_len = NonZeroU8::new(nid.len().try_into().unwrap()).unwrap();
        Ok(())
    }
    /// Percent-encoded NSS (Namespace-specific string) identifying the resource.
    ///
    /// For example, in `urn:ietf:rfc:2648`, `rfs:2648` is the NSS.
    ///
    /// **See also:** [`percent::decode_nss`]
    #[must_use]
    pub fn nss(&self) -> &str {
        &self.urn[self.nss_range()]
    }
    /// Set the NSS (must be [a valid NSS](https://datatracker.ietf.org/doc/html/rfc8141#section-2)
    /// and use percent-encoding).
    ///
    /// **See also:** [`percent::encode_nss`]
    ///
    /// # Errors
    /// Returns [`Error::InvalidNss`] in case of a validation failure.
    pub fn set_nss(&mut self, nss: &str) -> Result<()> {
        let mut nss = TriCow::Borrowed(nss);
        if nss.is_empty() || parse_nss(&mut nss, 0)? != nss.len() {
            return Err(Error::InvalidNss);
        }
        // unwrap: NSS length is non-zero as checked above
        let nss_len =
            NonZeroU32::new(nss.len().try_into().map_err(|_| Error::InvalidNss)?).unwrap();
        let range = self.nss_range();
        replace_range(&mut self.urn, range, &nss)?;
        self.nss_len = nss_len;
        Ok(())
    }
    /// Percent-encoded r-component, following the `?+` character sequence, to be used for passing
    /// parameters to URN resolution services.
    ///
    /// In `urn:example:foo-bar-baz-qux?+CCResolve:cc=uk`, the r-component is `CCResolve:cc=uk`.
    ///
    /// Should not be used for equivalence checks. As of the time of writing this, exact semantics
    /// aren't in the RFC.
    ///
    /// **See also:** [`percent::decode_r_component`]
    #[must_use]
    pub fn r_component(&self) -> Option<&str> {
        self.r_component_range().map(|range| &self.urn[range])
    }
    /// Set the r-component (must be [a valid
    /// r-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use
    /// percent-encoding).
    ///
    /// **See also:** [`percent::encode_r_component`]
    ///
    /// # Errors
    /// Returns [`Error::InvalidRComponent`] in case of a validation failure.
    pub fn set_r_component(&mut self, r_component: Option<&str>) -> Result<()> {
        if let Some(rc) = r_component {
            let mut rc = TriCow::Borrowed(rc);
            if rc.is_empty() || parse_r_component(&mut rc, 0)? != rc.len() {
                return Err(Error::InvalidRComponent);
            }
            let rc_len = rc.len().try_into().map_err(|_| Error::InvalidRComponent)?;
            let range = if let Some(range) = self.r_component_range() {
                range
            } else {
                // insert RCOMP_PREFIX if r-component doesn't already exist
                let nss_end = self.nss_range().end;
                replace_range(&mut self.urn, nss_end..nss_end, RCOMP_PREFIX)?;
                nss_end + RCOMP_PREFIX.len()..nss_end + RCOMP_PREFIX.len()
            };
            replace_range(&mut self.urn, range, &rc)?;
            self.r_component_len = Some(NonZeroU32::new(rc_len).unwrap());
        } else if let Some(mut range) = self.r_component_range() {
            range.start -= RCOMP_PREFIX.len();
            replace_range(&mut self.urn, range, "")?;
            self.r_component_len = None;
        }
        Ok(())
    }
    /// Percent-encoded q-component, following the `?=` character sequence. Has a similar function to the URL query
    /// string.
    ///
    /// In `urn:example:weather?=op=map&lat=39.56&lon=-104.85`,
    /// the q-component is `op=map&lat=39.56&lon=-104.85`.
    ///
    /// Should not be used for equivalence checks.
    ///
    /// **See also:** [`percent::decode_q_component`]
    #[must_use]
    pub fn q_component(&self) -> Option<&str> {
        self.q_component_range().map(|range| &self.urn[range])
    }
    /// Set the q-component (must be [a valid
    /// q-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use
    /// percent-encoding).
    ///
    /// **See also:** [`percent::encode_q_component`]
    ///
    /// # Errors
    /// Returns [`Error::InvalidQComponent`] in case of a validation failure.
    pub fn set_q_component(&mut self, q_component: Option<&str>) -> Result<()> {
        if let Some(qc) = q_component {
            let mut qc = TriCow::Borrowed(qc);
            if qc.is_empty() || parse_q_component(&mut qc, 0)? != qc.len() {
                return Err(Error::InvalidQComponent);
            }
            let qc_len = qc.len().try_into().map_err(|_| Error::InvalidQComponent)?;
            let range = if let Some(range) = self.q_component_range() {
                range
            } else {
                // insert QCOMP_PREFIX if q-component doesn't already exist
                let pre_qc_end = self.pre_q_component_end();
                replace_range(&mut self.urn, pre_qc_end..pre_qc_end, QCOMP_PREFIX)?;
                pre_qc_end + QCOMP_PREFIX.len()..pre_qc_end + QCOMP_PREFIX.len()
            };
            replace_range(&mut self.urn, range, &qc)?;
            self.q_component_len = Some(NonZeroU32::new(qc_len).unwrap());
        } else if let Some(mut range) = self.q_component_range() {
            range.start -= QCOMP_PREFIX.len();
            replace_range(&mut self.urn, range, "")?;
            self.q_component_len = None;
        }
        Ok(())
    }
    /// Percent-encoded f-component following the `#` character at the end of the URN. Has a
    /// similar function to the URL fragment.
    ///
    /// In `urn:example:a123,z456#789`, the f-component is `789`.
    ///
    /// Should not be used for equivalence checks.
    ///
    /// **See also:** [`percent::decode_f_component`]
    #[must_use]
    pub fn f_component(&self) -> Option<&str> {
        self.f_component_start().map(|start| &self.urn[start..])
    }
    /// Set the f-component (must be [a valid
    /// f-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use
    /// percent-encoding).
    ///
    /// **See also:** [`percent::encode_f_component`]
    ///
    /// # Errors
    /// Returns [`Error::InvalidFComponent`] in case of a validation failure.
    pub fn set_f_component(&mut self, f_component: Option<&str>) -> Result<()> {
        if let Some(fc) = f_component {
            let mut fc = TriCow::Borrowed(fc);
            if parse_f_component(&mut fc, 0)? != fc.len() {
                return Err(Error::InvalidFComponent);
            }
            let start = if let Some(start) = self.f_component_start() {
                start
            } else {
                let range = self.urn.len()..self.urn.len();
                replace_range(&mut self.urn, range, FCOMP_PREFIX)?;
                self.urn.len()
            };
            let len = self.urn.len();
            replace_range(&mut self.urn, start..len, &fc)?;
        } else if let Some(start) = self.f_component_start() {
            let len = self.urn.len();
            replace_range(&mut self.urn, start - FCOMP_PREFIX.len()..len, "")?;
        }
        Ok(())
    }
}

impl AsRef<[u8]> for UrnSlice<'_> {
    fn as_ref(&self) -> &[u8] {
        self.urn.as_bytes()
    }
}

impl AsRef<str> for UrnSlice<'_> {
    fn as_ref(&self) -> &str {
        &self.urn
    }
}

impl PartialEq for UrnSlice<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.urn[..self.nss_range().end] == other.urn[..other.nss_range().end]
    }
}

impl Eq for UrnSlice<'_> {}

impl Hash for UrnSlice<'_> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.urn[..self.nss_range().end].hash(state);
    }
}

impl fmt::Display for UrnSlice<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.write_str(&self.urn)
    }
}

#[cfg(feature = "alloc")]
impl FromStr for UrnSlice<'_> {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        parse_urn(TriCow::Owned(s.to_owned()))
    }
}

impl<'a> TryFrom<&'a str> for UrnSlice<'a> {
    type Error = Error;
    fn try_from(value: &'a str) -> Result<Self> {
        parse_urn(TriCow::Borrowed(value))
    }
}

impl<'a> TryFrom<&'a mut str> for UrnSlice<'a> {
    type Error = Error;
    fn try_from(value: &'a mut str) -> Result<Self> {
        parse_urn(TriCow::MutBorrowed(value))
    }
}

#[cfg(feature = "alloc")]
impl TryFrom<String> for UrnSlice<'static> {
    type Error = Error;
    fn try_from(value: String) -> Result<Self> {
        parse_urn(TriCow::Owned(value))
    }
}

#[cfg(all(feature = "serde", feature = "alloc"))]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> serde::Deserialize<'de> for UrnSlice<'static> {
    fn deserialize<D>(de: D) -> Result<Self, <D as serde::Deserializer<'de>>::Error>
    where
        D: serde::Deserializer<'de>,
    {
        UrnSlice::try_from(String::deserialize(de)?).map_err(serde::de::Error::custom)
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl serde::Serialize for UrnSlice<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
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
    ///
    /// - `nid`: the namespace identifier
    /// - `nss`: the percent-encoded NSS (namespace-specific string)
    ///
    /// **See also:** [`percent::encode_nss`]
    pub fn new(nid: &'a str, nss: &'a str) -> Self {
        Self {
            nid,
            nss,
            r_component: None,
            q_component: None,
            f_component: None,
        }
    }
    /// Change the namespace identifier.
    pub fn nid(mut self, nid: &'a str) -> Self {
        self.nid = nid;
        self
    }
    /// Change the namespace-specific string (must be percent encoded).
    ///
    /// **See also:** [`percent::encode_nss`]
    pub fn nss(mut self, nss: &'a str) -> Self {
        self.nss = nss;
        self
    }
    /// Change the r-component (must be percent encoded).
    ///
    /// **See also:** [`percent::encode_r_component`]
    pub fn r_component(mut self, r_component: Option<&'a str>) -> Self {
        self.r_component = r_component;
        self
    }
    /// Change the q-component (must be percent encoded).
    ///
    /// **See also:** [`percent::encode_q_component`]
    pub fn q_component(mut self, q_component: Option<&'a str>) -> Self {
        self.q_component = q_component;
        self
    }
    /// Change the f-component (must be percent encoded).
    ///
    /// **See also:** [`percent::encode_f_component`]
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
    pub fn build(self) -> Result<UrnSlice<'static>> {
        fn cow_push_str(c: &mut TriCow, s: &str) {
            if let TriCow::Owned(c) = c {
                c.push_str(s);
            } else {
                unreachable!("cow must be owned to use this function")
            }
        }
        if !is_valid_nid(self.nid) {
            return Err(Error::InvalidNid);
        }
        let mut s = TriCow::Owned(URN_PREFIX.to_owned());
        {
            let s = &mut s;
            cow_push_str(s, self.nid);
            cow_push_str(s, NID_NSS_SEPARATOR);
            let nss_start = s.len();
            cow_push_str(s, self.nss);
            if self.nss.is_empty() || parse_nss(s, nss_start)? != s.len() {
                return Err(Error::InvalidNss);
            }
            if let Some(rc) = self.r_component {
                cow_push_str(s, RCOMP_PREFIX);
                let rc_start = s.len();
                cow_push_str(s, rc);
                if rc.is_empty() || parse_r_component(s, rc_start)? != s.len() {
                    return Err(Error::InvalidRComponent);
                }
            }
            if let Some(qc) = self.q_component {
                cow_push_str(s, QCOMP_PREFIX);
                let qc_start = s.len();
                cow_push_str(s, qc);
                if qc.is_empty() || parse_q_component(s, qc_start)? != s.len() {
                    return Err(Error::InvalidQComponent);
                }
            }
            if let Some(fc) = self.f_component {
                cow_push_str(s, FCOMP_PREFIX);
                let fc_start = s.len();
                cow_push_str(s, fc);
                if parse_f_component(s, fc_start)? != s.len() {
                    return Err(Error::InvalidFComponent);
                }
            }
        }
        Ok(UrnSlice {
            // we already had to allocate since we use a builder, obviously allocations are allowed
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
        UrnSlice::try_from("6򭞦*�").unwrap_err();
        #[cfg(feature = "alloc")]
        assert_eq!(
            UrnSlice::try_from("urn:nbn:de:bvb:19-146642").unwrap(),
            UrnBuilder::new("nbn", "de:bvb:19-146642").build().unwrap()
        );
        assert_eq!(
            UrnSlice::try_from("urn:nbn:de:bvb:19-146642")
                .unwrap()
                .to_string(),
            "urn:nbn:de:bvb:19-146642"
        );

        #[cfg(feature = "alloc")]
        assert_eq!(
            UrnSlice::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test").unwrap(),
            UrnBuilder::new("example", "foo-bar-baz-qux")
                .r_component(Some("CCResolve:cc=uk"))
                .f_component(Some("test"))
                .build()
                .unwrap()
        );
        assert_eq!(
            UrnSlice::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test")
                .unwrap()
                .f_component()
                .unwrap(),
            "test"
        );
        assert_eq!(
            UrnSlice::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test")
                .unwrap()
                .r_component()
                .unwrap(),
            "CCResolve:cc=uk"
        );
        assert_eq!(
            UrnSlice::try_from("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test")
                .unwrap()
                .to_string(),
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test",
        );

        #[cfg(feature = "alloc")]
        assert_eq!(
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
                .parse::<UrnSlice>()
                .unwrap(),
            UrnBuilder::new("example", "weather")
                .q_component(Some(
                    "op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
                ))
                .build()
                .unwrap()
        );
        assert_eq!(
            UrnSlice::try_from(
                "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
            )
            .unwrap()
            .to_string(),
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
        );

        #[cfg(feature = "alloc")]
        assert_eq!(
            "uRn:eXaMpLe:%3d%3a?=aoiwnfuafo"
                .parse::<UrnSlice>()
                .unwrap(),
            UrnBuilder::new("example", "%3D%3a").build().unwrap()
        );
        let mut arr = *b"uRn:eXaMpLe:%3d%3a?=aoiwnfuafo";
        assert_eq!(
            UrnSlice::try_from(core::str::from_utf8_mut(&mut arr[..]).unwrap())
                .unwrap()
                .as_str(),
            "urn:example:%3D%3A?=aoiwnfuafo",
        );

        assert_eq!(
            UrnSlice::try_from("urn:-example:abcd"),
            Err(Error::InvalidNid)
        );
        assert_eq!(
            UrnSlice::try_from("urn:example:/abcd"),
            Err(Error::InvalidNss)
        );
        assert_eq!(UrnSlice::try_from("urn:a:abcd"), Err(Error::InvalidNid));
        assert_eq!(
            UrnSlice::try_from("urn:0123456789abcdef0123456789abcdef0:abcd"),
            Err(Error::InvalidNid)
        );
        let _ = UrnSlice::try_from("urn:0123456789abcdef0123456789abcdef:abcd").unwrap();
        assert_eq!(UrnSlice::try_from("urn:example"), Err(Error::InvalidNss));
        assert_eq!(UrnSlice::try_from("urn:example:"), Err(Error::InvalidNss));
        assert_eq!(UrnSlice::try_from("urn:example:%"), Err(Error::InvalidNss));
        assert_eq!(UrnSlice::try_from("urn:example:%a"), Err(Error::InvalidNss));
        assert_eq!(
            UrnSlice::try_from("urn:example:%a_"),
            Err(Error::InvalidNss)
        );
        let mut arr = *b"urn:example:%a0?+";
        assert_eq!(
            UrnSlice::try_from(core::str::from_utf8_mut(&mut arr[..]).unwrap()),
            Err(Error::InvalidRComponent)
        );
        let mut arr = *b"urn:example:%a0?+%a0?=";
        assert_eq!(
            UrnSlice::try_from(core::str::from_utf8_mut(&mut arr[..]).unwrap()),
            Err(Error::InvalidQComponent)
        );
        let mut arr = *b"urn:example:%a0?+%a0?=a";
        assert_eq!(
            UrnSlice::try_from(core::str::from_utf8_mut(&mut arr[..]).unwrap())
                .unwrap()
                .r_component()
                .unwrap(),
            "%A0",
        );

        #[cfg(feature = "alloc")]
        {
            let mut urn = "urn:example:test".parse::<UrnSlice>().unwrap();
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
