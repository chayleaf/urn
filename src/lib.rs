//! A crate for handling [URNs](https://datatracker.ietf.org/doc/html/rfc8141).
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
//! assert_eq!(urn.to_string(), "urn:example:1234:5678");
//! assert_eq!(urn, "urn:example:1234:5678".parse()?); // Using std::str::parse
//! # Ok(())
//! # }
//! ```
#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::{
    borrow::{Cow, ToOwned},
    fmt,
    string::String,
};
use core::{
    convert::TryFrom,
    hash::{self, Hash},
    num::NonZeroUsize,
    ops::{Deref, Range, RangeBounds},
    result,
    slice::SliceIndex,
    str::FromStr,
};
#[cfg(feature = "std")]
use std::{borrow::Cow, fmt};

#[repr(u8)]
#[derive(Debug, PartialEq, Eq)]
/// A helper enum for [`replace_case`]
enum Case {
    Lower = 0,
    Upper = 1,
}

/// Make all ascii letters in range uppercase (or lowercase)
fn replace_case<R, const UPPER: u8>(c: &mut Cow<str>, range: R)
where
    R: Clone + RangeBounds<usize> + SliceIndex<str>,
    R::Output: AsRef<str> + AsMut<str>,
{
    let needs_fixing = (&c[range.clone()]).as_ref().bytes().any(|b| {
        if UPPER != 0 {
            b.is_ascii_lowercase()
        } else {
            b.is_ascii_uppercase()
        }
    });
    if needs_fixing {
        if let Cow::Borrowed(s) = c {
            *c = s.to_owned().into();
        }
        if let Cow::Owned(s) = c {
            let s = s.as_mut_str()[range].as_mut();
            if UPPER != 0 {
                s.make_ascii_uppercase();
            } else {
                s.make_ascii_lowercase();
            }
        }
    }
}

/// Checks whether a string is a valid NID
fn is_valid_nid(s: &str) -> bool {
    s.len() >= 2
        && !s.starts_with('-')
        && !s.ends_with('-')
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || (b as char) == '-')
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum PEncoded {
    Nss,
    RComponent,
    QComponent,
    FComponent,
}

/// Must be a valid percent-encoded string already. Returns the end.
fn parse_encoded(s: &mut Cow<str>, start: usize, kind: PEncoded) -> usize {
    let mut it = start..s.len();
    while let Some(i) = it.next() {
        match (kind, s.bytes().nth(i).unwrap() as char) {
            (PEncoded::FComponent, '?') if i == start => {}
            // ?= terminates the r-component despite otherwise being a valid part of r-component
            (PEncoded::RComponent, '?')
                if i != start
                    && s.bytes()
                        .nth(i + 1)
                        .map(|b| b as char != '=')
                        .unwrap_or(true) => {}
            (PEncoded::QComponent, '?') if i != start => {}
            (PEncoded::FComponent, '?') if i != start => {}
            (PEncoded::FComponent, '/') if i == start => {}
            (_, '/') if i != start => {}
            (
                _,
                '-' | '.' | '_' | '~' | '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';'
                | '=' | ':' | '@',
            ) => {}
            (_, c) if c.is_ascii_alphanumeric() => {}
            (_, '%')
                if i + 2 < s.bytes().len()
                    && s.bytes().skip(i + 1).take(2).all(|c| c.is_ascii_hexdigit()) =>
            {
                replace_case::<_, { Case::Upper as u8 }>(s, i + 1..i + 3);
                it.next();
                it.next();
            }
            (_, _) => return i,
        }
    }
    s.len()
}

/// Returns the end
fn parse_nss(s: &mut Cow<str>, start: usize) -> usize {
    parse_encoded(s, start, PEncoded::Nss)
}

/// Returns the end
fn parse_r_component(s: &mut Cow<str>, start: usize) -> usize {
    parse_encoded(s, start, PEncoded::RComponent)
}

/// Returns the end
fn parse_q_component(s: &mut Cow<str>, start: usize) -> usize {
    parse_encoded(s, start, PEncoded::QComponent)
}

/// Returns the end
fn parse_f_component(s: &mut Cow<str>, start: usize) -> usize {
    parse_encoded(s, start, PEncoded::FComponent)
}

fn parse_urn(mut s: Cow<str>) -> Result<Urn> {
    if s.len() < 4 {
        return Err(Error::InvalidScheme);
    }

    replace_case::<_, { Case::Lower as u8 }>(&mut s, ..4);

    if &s[..4] != "urn:" {
        return Err(Error::InvalidScheme);
    }

    let nid_start = 4;
    let nid_end = s
        .bytes()
        .enumerate()
        .skip(nid_start)
        .find(|(_, b)| *b as char == ':')
        .map(|(i, _)| i);

    // If NID is valid but NSS is completely missing (including the :), return NSS error instead of NID error
    if nid_end.is_none() && is_valid_nid(&s[nid_start..]) {
        return Err(Error::InvalidNss);
    }
    let nid_end = nid_end
        .filter(|nid_end| is_valid_nid(&s[nid_start..*nid_end]))
        .ok_or(Error::InvalidNid)?;
    replace_case::<_, { Case::Lower as u8 }>(&mut s, nid_start..nid_end);

    let nss_start = nid_end + 1;
    let nss_end = parse_nss(&mut s, nss_start);
    if nss_end == nss_start {
        return Err(Error::InvalidNss);
    }

    let mut end = nss_end;
    let mut leftover_error = Error::InvalidNss;

    let r_component_len = if s[end..].starts_with("?+") {
        let rc_start = end + 2;
        let rc_end = parse_r_component(&mut s, rc_start);
        end = rc_end;
        leftover_error = Error::InvalidRComponent;
        Some(NonZeroUsize::new(rc_end - rc_start).ok_or(Error::InvalidRComponent)?)
    } else {
        None
    };

    let q_component_len = if s[end..].starts_with("?=") {
        let qc_start = end + 2;
        let qc_end = parse_q_component(&mut s, qc_start);
        end = qc_end;
        leftover_error = Error::InvalidQComponent;
        Some(NonZeroUsize::new(qc_end - qc_start).ok_or(Error::InvalidQComponent)?)
    } else {
        None
    };

    if s[end..].starts_with('#') {
        let fc_start = end + 1;
        let fc_end = parse_f_component(&mut s, fc_start);
        end = fc_end;
        leftover_error = Error::InvalidFComponent;
    }

    if end < s.len() {
        return Err(leftover_error);
    }

    Ok(Urn {
        urn: s.into_owned(),
        nid_len: NonZeroUsize::new(nid_end - nid_start).unwrap(),
        nss_len: NonZeroUsize::new(nss_end - nss_start).unwrap(),
        r_component_len,
        q_component_len,
    })
}

/// A URN validation error.
#[derive(Debug, PartialEq, Eq)]
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
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Error::InvalidScheme => "invalid urn scheme",
            Error::InvalidNid => "invalid urn namespace id",
            Error::InvalidNss => "invalid urn namespace-specific string",
            Error::InvalidRComponent => "invalid urn r-component",
            Error::InvalidQComponent => "invalid urn q-component",
            Error::InvalidFComponent => "invalid urn f-component (fragment)",
        })
    }
}

type Result<T> = result::Result<T, Error>;

#[cfg(feature = "std")]
impl std::error::Error for Error {}

/// An RFC2141/8141 URN (Uniform Resource Name).
///
/// **Note:** the equivalence checks are done
/// [according to the specification](https://www.rfc-editor.org/rfc/rfc8141.html#section-3),
/// only taking the NID and NSS into account! If you need exact equivalence checks, consider
/// comparing using `Urn::as_str()` as the key. Some namespaces may define additional lexical
/// equivalence checks, these aren't accounted for in this implementation.
#[derive(Debug)]
pub struct Urn {
    // Entire URN string
    urn: String,
    nid_len: NonZeroUsize,
    nss_len: NonZeroUsize,
    r_component_len: Option<NonZeroUsize>,
    q_component_len: Option<NonZeroUsize>,
}

impl Urn {
    fn nid_range(&self) -> Range<usize> {
        // urn:<nid>
        4..4 + self.nid_len.get()
    }

    fn nss_range(&self) -> Range<usize> {
        // urn:<nid>:<nss>
        let start = self.nid_range().end + 1;
        start..start + self.nss_len.get()
    }

    fn r_component_range(&self) -> Option<Range<usize>> {
        self.r_component_len.map(|r_component_len| {
            // urn:<nid>:<nss>[?+<r-component>]
            let start = self.nss_range().end + 2;
            start..start + r_component_len.get()
        })
    }

    fn q_component_range(&self) -> Option<Range<usize>> {
        self.q_component_len.map(|q_component_len| {
            // urn:<nid>:<nss>[?+<r-component>][?=<q-component>]
            let start = self
                .r_component_range()
                .unwrap_or_else(|| self.nss_range())
                .end
                + 2;
            start..start + q_component_len.get()
        })
    }

    fn f_component_start(&self) -> Option<usize> {
        let pre_fc = self
            .q_component_range()
            .or_else(|| self.r_component_range())
            .unwrap_or_else(|| self.nss_range())
            .end;
        (pre_fc < self.urn.len()).then(|| {
            // urn:<nid>:<nss>[?+<r-component>][?=<q-component>][#<f-component>]
            pre_fc + 1
        })
    }

    /// String representation of the current URN (Canonicized).
    pub fn as_str(&self) -> &str {
        &self.urn
    }

    /// NID (Namespace identifier), the first part of the URN.
    ///
    /// For example, in `urn:ietf:rfc:2648`, `ietf` is the namespace.
    pub fn nid(&self) -> &str {
        &self.urn[self.nid_range()]
    }
    /// Set the NID (must be [a valid NID](https://datatracker.ietf.org/doc/html/rfc8141#section-2)).
    pub fn set_nid(&mut self, nid: &str) -> Result<()> {
        if !is_valid_nid(nid) {
            return Err(Error::InvalidNid);
        }
        let mut nid = nid.into();
        replace_case::<_, { Case::Lower as u8 }>(&mut nid, ..);
        self.urn.replace_range(self.nid_range(), &nid);
        self.nid_len = NonZeroUsize::new(nid.len()).unwrap();
        Ok(())
    }
    /// NSS (Namespace-specific string) identifying the resource.
    ///
    /// For example, in `urn:ietf:rfc:2648`, `rfs:2648` is the NSS.
    pub fn nss(&self) -> &str {
        &self.urn[self.nss_range()]
    }
    /// Set the namespace-specific string (must be [a valid NSS](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    pub fn set_nss(&mut self, nss: &str) -> Result<()> {
        let mut nss = Cow::from(nss);
        if nss.is_empty() || parse_nss(&mut nss, 0) != nss.len() {
            return Err(Error::InvalidNss);
        }
        self.urn.replace_range(self.nss_range(), &nss);
        self.nss_len = NonZeroUsize::new(nss.len()).unwrap();
        Ok(())
    }
    /// r-component, following the `?+` character sequence, to be used for passing parameters
    /// to URN resolution services.
    ///
    /// In `urn:example:foo-bar-baz-qux?+CCResolve:cc=uk`, `CCResolve:cc=uk` is the r-component.
    ///
    /// Should not be used for equivalence checks. As of 2021, exact semantics are undefined.
    pub fn r_component(&self) -> Option<&str> {
        self.r_component_range().map(|range| &self.urn[range])
    }
    /// Set the r-component (must be [a valid r-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    pub fn set_r_component(&mut self, r_component: Option<&str>) -> Result<()> {
        let range = self
            .r_component_range()
            .map(|mut r| {
                r.start -= 2;
                r
            })
            .unwrap_or_else(|| {
                let nss_end = self.nss_range().end;
                nss_end..nss_end
            });
        if let Some(rc) = r_component {
            let mut rc = Cow::from(rc);
            if rc.is_empty() || parse_r_component(&mut rc, 0) != rc.len() {
                return Err(Error::InvalidRComponent);
            }
            self.urn.replace_range(range, &("?+".to_owned() + &rc));
            self.r_component_len = Some(NonZeroUsize::new(rc.len()).unwrap());
        } else {
            self.urn.replace_range(range, "");
            self.r_component_len = None;
        }
        Ok(())
    }
    /// q-component, following the `?=` character sequence. Has a similar function to the URL query
    /// string.
    ///
    /// Should not be used for equivalence checks.
    pub fn q_component(&self) -> Option<&str> {
        self.q_component_range().map(|range| &self.urn[range])
    }
    /// Set the q-component (must be [a valid q-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    pub fn set_q_component(&mut self, q_component: Option<&str>) -> Result<()> {
        let range = self
            .q_component_range()
            .map(|mut r| {
                r.start -= 2;
                r
            })
            .or_else(|| self.r_component_range().map(|r| r.end..r.end))
            .unwrap_or_else(|| {
                let nss_end = self.nss_range().end;
                nss_end..nss_end
            });
        if let Some(qc) = q_component {
            let mut qc = Cow::from(qc);
            if qc.is_empty() || parse_q_component(&mut qc, 0) != qc.len() {
                return Err(Error::InvalidQComponent);
            }
            self.urn.replace_range(range, &("?=".to_owned() + &qc));
            self.q_component_len = Some(NonZeroUsize::new(qc.len()).unwrap());
        } else {
            self.urn.replace_range(range, "");
            self.q_component_len = None;
        }
        Ok(())
    }
    /// f-component (fragment) following the `#` character at the end of the URN.
    ///
    /// Should not be used for equivalence checks.
    pub fn f_component(&self) -> Option<&str> {
        self.f_component_start().map(|start| &self.urn[start..])
    }
    /// Set the f-component (must be [a valid f-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    pub fn set_f_component(&mut self, f_component: Option<&str>) -> Result<()> {
        let start = self
            .f_component_start()
            .map(|s| s - 1)
            .unwrap_or_else(|| self.urn.len());
        if let Some(fc) = f_component {
            let mut fc = fc.into();
            if parse_f_component(&mut fc, 0) != fc.len() {
                return Err(Error::InvalidFComponent);
            }
            self.urn.replace_range(start.., &("#".to_owned() + &fc));
        } else {
            self.urn.replace_range(start.., "");
        }
        Ok(())
    }
}

impl Deref for Urn {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        &self.urn
    }
}

impl AsRef<[u8]> for Urn {
    fn as_ref(&self) -> &[u8] {
        self.urn.as_ref()
    }
}

impl AsRef<str> for Urn {
    fn as_ref(&self) -> &str {
        &self.urn
    }
}

impl PartialEq for Urn {
    fn eq(&self, other: &Self) -> bool {
        self.urn[..self.nss_range().end] == other.urn[..other.nss_range().end]
    }
}

impl Eq for Urn {}

impl Hash for Urn {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.urn[..self.nss_range().end].hash(state);
    }
}

impl fmt::Display for Urn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {
        f.write_str(&self.urn)
    }
}

impl FromStr for Urn {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        parse_urn(s.into())
    }
}

impl TryFrom<&str> for Urn {
    type Error = Error;
    fn try_from(value: &str) -> Result<Self> {
        value.parse()
    }
}

impl TryFrom<String> for Urn {
    type Error = Error;
    fn try_from(value: String) -> Result<Self> {
        parse_urn(value.into())
    }
}

/// A struct used for constructing URNs.
#[derive(Debug)]
pub struct UrnBuilder {
    nid: String,
    nss: String,
    r_component: Option<String>,
    q_component: Option<String>,
    f_component: Option<String>,
}

impl UrnBuilder {
    /// Create a new UrnBuilder.
    pub fn new(nid: &str, nss: &str) -> Self {
        Self {
            nid: nid.to_owned(),
            nss: nss.to_owned(),
            r_component: None,
            q_component: None,
            f_component: None,
        }
    }
    /// Change the namespace.
    pub fn namespace(mut self, nid: &str) -> Self {
        self.nid = nid.to_owned();
        self
    }
    /// Change the namespace-specific string.
    pub fn nss(mut self, nss: &str) -> Self {
        self.nss = nss.to_owned();
        self
    }
    /// Change the r-component.
    pub fn r_component(mut self, r_component: &str) -> Self {
        self.r_component = Some(r_component.to_owned());
        self
    }
    /// Change the q-component.
    pub fn q_component(mut self, q_component: &str) -> Self {
        self.q_component = Some(q_component.to_owned());
        self
    }
    /// Change the f-component.
    pub fn f_component(mut self, f_component: &str) -> Self {
        self.f_component = Some(f_component.to_owned());
        self
    }
    /// [Validate the data](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and create the URN.
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
    /// assert_eq!(urn.to_string(), "urn:example:1234:5678");
    /// assert_eq!(urn, "urn:example:1234:5678".parse()?); // Using std::str::parse
    /// # Ok(())
    /// # }
    /// ```
    pub fn build(self) -> Result<Urn> {
        let mut s = "urn:".to_owned();
        s.push_str(&self.nid);
        s.push(':');
        s.push_str(&self.nss);
        if let Some(rc) = self.r_component {
            if !rc.is_empty() {
                s.push_str("?+");
                s.push_str(&rc);
            } else {
                return Err(Error::InvalidRComponent);
            }
        }
        if let Some(qc) = self.q_component {
            if !qc.is_empty() {
                s.push_str("?=");
                s.push_str(&qc);
            } else {
                return Err(Error::InvalidQComponent);
            }
        }
        if let Some(fc) = self.f_component {
            s.push('#');
            s.push_str(&fc);
        }
        s.parse()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(feature = "std"))]
    use super::alloc::string::ToString;

    #[test]
    fn it_works() {
        assert_eq!(
            "urn:nbn:de:bvb:19-146642".parse::<Urn>().unwrap(),
            UrnBuilder::new("nbn", "de:bvb:19-146642").build().unwrap()
        );
        assert_eq!(
            "urn:nbn:de:bvb:19-146642"
                .parse::<Urn>()
                .unwrap()
                .to_string(),
            "urn:nbn:de:bvb:19-146642"
        );

        assert_eq!(
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test"
                .parse::<Urn>()
                .unwrap(),
            UrnBuilder::new("example", "foo-bar-baz-qux")
                .r_component("CCResolve:cc=uk")
                .f_component("test")
                .build()
                .unwrap()
        );
        assert_eq!(
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test"
                .parse::<Urn>()
                .unwrap()
                .f_component()
                .unwrap(),
            "test"
        );
        assert_eq!(
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test"
                .parse::<Urn>()
                .unwrap()
                .r_component()
                .unwrap(),
            "CCResolve:cc=uk"
        );
        assert_eq!(
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test"
                .parse::<Urn>()
                .unwrap()
                .to_string(),
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test",
        );

        assert_eq!(
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
                .parse::<Urn>()
                .unwrap(),
            UrnBuilder::new("example", "weather")
                .q_component("op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z")
                .build()
                .unwrap()
        );
        assert_eq!(
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
                .parse::<Urn>()
                .unwrap()
                .to_string(),
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
        );

        assert_eq!(
            "uRn:eXaMpLe:%3d%3a?=aoiwnfuafo".parse::<Urn>().unwrap(),
            UrnBuilder::new("example", "%3D%3a").build().unwrap()
        );
        assert_eq!(
            "uRn:eXaMpLe:%3d%3a?=aoiwnfuafo"
                .parse::<Urn>()
                .unwrap()
                .to_string(),
            "urn:example:%3D%3A?=aoiwnfuafo",
        );

        assert_eq!("urn:-example:abcd".parse::<Urn>(), Err(Error::InvalidNid));
        assert_eq!("urn:example:/abcd".parse::<Urn>(), Err(Error::InvalidNss));
        assert_eq!("urn:a:abcd".parse::<Urn>(), Err(Error::InvalidNid));
        assert_eq!("urn:example".parse::<Urn>(), Err(Error::InvalidNss));
        assert_eq!("urn:example:".parse::<Urn>(), Err(Error::InvalidNss));
        assert_eq!("urn:example:%".parse::<Urn>(), Err(Error::InvalidNss));
        assert_eq!("urn:example:%a".parse::<Urn>(), Err(Error::InvalidNss));
        assert_eq!("urn:example:%a_".parse::<Urn>(), Err(Error::InvalidNss));
        assert_eq!(
            "urn:example:%a0?+".parse::<Urn>(),
            Err(Error::InvalidRComponent)
        );
        assert_eq!(
            "urn:example:%a0?+%a0?=".parse::<Urn>(),
            Err(Error::InvalidQComponent)
        );
        assert_eq!(
            "urn:example:%a0?+%a0?=a".parse::<Urn>().unwrap().r_component().unwrap(),
            "%A0",
        );

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
