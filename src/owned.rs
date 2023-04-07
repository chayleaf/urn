use crate::{Error, Result, UrnSlice};
#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::{borrow::ToOwned, string::String};
use core::{fmt, ops::Deref, str::FromStr};

/// An RFC2141/8141 URN (Uniform Resource Name).
///
/// **Note:** the equivalence checks are done
/// [according to the specification](https://www.rfc-editor.org/rfc/rfc8141.html#section-3),
/// only taking the NID and NSS into account! If you need exact equivalence checks, consider
/// comparing using `Urn::as_str()` as the key. Some namespaces may define additional lexical
/// equivalence rules, these aren't accounted for in this implementation (Meaning there might be
/// false negatives for some namespaces). There will, however, be no false positives.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Urn(UrnSlice<'static>);

impl Deref for Urn {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

impl AsRef<[u8]> for Urn {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl AsRef<str> for Urn {
    fn as_ref(&self) -> &str {
        self.0.as_ref()
    }
}

impl fmt::Display for Urn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        self.0.fmt(f)
    }
}

impl FromStr for Urn {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        Ok(Self(UrnSlice::from_str(s)?))
    }
}

impl<'a> TryFrom<&'a str> for Urn {
    type Error = Error;
    fn try_from(value: &'a str) -> Result<Self> {
        Ok(Self(UrnSlice::try_from(value.to_owned())?))
    }
}

impl<'a> TryFrom<&'a mut str> for Urn {
    type Error = Error;
    fn try_from(value: &'a mut str) -> Result<Self> {
        Ok(Self(UrnSlice::try_from(value.to_owned())?))
    }
}

impl TryFrom<String> for Urn {
    type Error = Error;
    fn try_from(value: String) -> Result<Self> {
        Ok(Self(UrnSlice::try_from(value)?))
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl<'de> serde::Deserialize<'de> for Urn {
    fn deserialize<D>(de: D) -> Result<Self, <D as serde::Deserializer<'de>>::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self(UrnSlice::deserialize(de)?))
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
impl serde::Serialize for Urn {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.0.serialize(serializer)
    }
}

impl Urn {
    /// String representation of this URN (Canonicized).
    #[must_use]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
    /// NID (Namespace identifier), the first part of the URN.
    ///
    /// For example, in `urn:ietf:rfc:2648`, `ietf` is the namespace.
    #[must_use]
    pub fn nid(&self) -> &str {
        self.0.nid()
    }
    /// Set the NID (must be [a valid NID](https://datatracker.ietf.org/doc/html/rfc8141#section-2)).
    /// # Errors
    /// Returns [`Error::InvalidNid`] in case of a validation failure.
    pub fn set_nid(&mut self, nid: &str) -> Result<()> {
        self.0.set_nid(nid)
    }
    /// NSS (Namespace-specific string) identifying the resource.
    ///
    /// For example, in `urn:ietf:rfc:2648`, `rfs:2648` is the NSS.
    #[must_use]
    pub fn nss(&self) -> &str {
        self.0.nss()
    }
    /// Set the NSS (must be [a valid NSS](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidNss`] in case of a validation failure.
    pub fn set_nss(&mut self, nss: &str) -> Result<()> {
        self.0.set_nss(nss)
    }
    /// r-component, following the `?+` character sequence, to be used for passing parameters
    /// to URN resolution services.
    ///
    /// In `urn:example:foo-bar-baz-qux?+CCResolve:cc=uk`, the r-component is `CCResolve:cc=uk`.
    ///
    /// Should not be used for equivalence checks. As of the time of writing this, exact semantics are undefined.
    #[must_use]
    pub fn r_component(&self) -> Option<&str> {
        self.0.r_component()
    }
    /// Set the r-component (must be [a valid r-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidRComponent`] in case of a validation failure.
    pub fn set_r_component(&mut self, r_component: Option<&str>) -> Result<()> {
        self.0.set_r_component(r_component)
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
        self.0.q_component()
    }
    /// Set the q-component (must be [a valid q-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidQComponent`] in case of a validation failure.
    pub fn set_q_component(&mut self, q_component: Option<&str>) -> Result<()> {
        self.0.set_q_component(q_component)
    }
    /// f-component following the `#` character at the end of the URN. Has a similar function to
    /// the URL fragment.
    ///
    /// In `urn:example:a123,z456#789`, the f-component is `789`.
    ///
    /// Should not be used for equivalence checks.
    #[must_use]
    pub fn f_component(&self) -> Option<&str> {
        self.0.f_component()
    }
    /// Set the f-component (must be [a valid f-component](https://datatracker.ietf.org/doc/html/rfc8141#section-2) and use percent-encoding).
    /// # Errors
    /// Returns [`Error::InvalidFComponent`] in case of a validation failure.
    pub fn set_f_component(&mut self, f_component: Option<&str>) -> Result<()> {
        self.0.set_f_component(f_component)
    }
}
