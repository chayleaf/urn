use crate::{Error, Result, UrnSlice};
#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::{borrow::ToOwned, string::String};
use core::{fmt, ops::{Deref, DerefMut}, str::FromStr};

/// An owned RFC2141/8141 URN (Uniform Resource Name).
///
/// **Note:** the equivalence checks are done
/// [according to the specification](https://www.rfc-editor.org/rfc/rfc8141.html#section-3),
/// only taking the NID and NSS into account! If you need exact equivalence checks, consider
/// comparing using `Urn::as_str()` as the key. Some namespaces may define additional lexical
/// equivalence rules, these aren't accounted for in this implementation (Meaning there might be
/// false negatives for some namespaces). There will, however, be no false positives.
///
/// `FromStr` requires a single allocation, but `TryFrom<String>` doesn't, so prefer `TryFrom` when
/// possible.
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Urn(UrnSlice<'static>);

impl fmt::Debug for Urn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Deref for Urn {
    type Target = UrnSlice<'static>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Urn {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a> AsRef<UrnSlice<'a>> for Urn {
    fn as_ref(&self) -> &UrnSlice<'a> {
        &self.0
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
