#[cfg(all(not(feature = "std"), feature = "alloc"))]
use alloc::{borrow::ToOwned, string::String};
use core::{fmt, ops::Deref, slice::SliceIndex};

#[cfg(not(feature = "alloc"))]
use super::Error;
use super::Result;

pub enum TriCow<'a> {
    #[cfg(feature = "alloc")]
    Owned(String),
    Borrowed(&'a str),
    MutBorrowed(&'a mut str),
}

impl fmt::Debug for TriCow<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            #[cfg(feature = "alloc")]
            Self::Owned(ref o) => fmt::Debug::fmt(o, f),
            Self::Borrowed(ref b) => fmt::Debug::fmt(b, f),
            Self::MutBorrowed(ref b) => fmt::Debug::fmt(b, f),
        }
    }
}

impl Clone for TriCow<'_> {
    fn clone(&self) -> Self {
        match self {
            #[cfg(feature = "alloc")]
            Self::MutBorrowed(s) => Self::Owned((*s).to_owned()),
            #[cfg(not(feature = "alloc"))]
            Self::MutBorrowed(_) => panic!("can't clone a urn that mutably borrows a string slice"),
            #[cfg(feature = "alloc")]
            Self::Owned(s) => Self::Owned(s.clone()),
            Self::Borrowed(s) => Self::Borrowed(s),
        }
    }
}

impl Deref for TriCow<'_> {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        match self {
            #[cfg(feature = "alloc")]
            Self::Owned(s) => s,
            Self::Borrowed(s) => s,
            Self::MutBorrowed(s) => s,
        }
    }
}

#[allow(clippy::unnecessary_wraps)]
pub fn replace_range(c: &mut TriCow, range: core::ops::Range<usize>, with: &str) -> Result<()> {
    match c {
        #[cfg(feature = "alloc")]
        TriCow::Owned(s) => {
            s.replace_range(range, with);
            Ok(())
        }
        #[cfg(feature = "alloc")]
        TriCow::Borrowed(s) => {
            let mut s = s.to_owned();
            s.replace_range(range, with);
            *c = TriCow::Owned(s);
            Ok(())
        }
        #[cfg(not(feature = "alloc"))]
        TriCow::Borrowed(_) => Err(Error::AllocRequired),
        TriCow::MutBorrowed(s) => {
            if range.len() == with.len() {
                #[cfg_attr(not(feature = "alloc"), allow(clippy::redundant_clone))]
                if let Some(slice) = s.get_mut(range.clone()) {
                    // SAFETY: both slice and with are valid utf-8 strings of same length
                    unsafe { slice.as_bytes_mut() }.copy_from_slice(with.as_bytes());
                    return Ok(());
                }
            }
            #[cfg(feature = "alloc")]
            {
                let mut s = s.to_owned();
                s.replace_range(range, with);
                *c = TriCow::Owned(s);
                Ok(())
            }
            #[cfg(not(feature = "alloc"))]
            Err(Error::AllocRequired)
        }
    }
}

pub fn cow_mut_ref<'a>(c: &'a mut TriCow) -> Result<&'a mut str> {
    match c {
        #[cfg(feature = "alloc")]
        TriCow::Owned(s) => Ok(s.as_mut_str()),
        #[cfg(feature = "alloc")]
        TriCow::Borrowed(s) => {
            *c = TriCow::Owned(s.to_owned());
            if let TriCow::Owned(s) = c {
                Ok(s.as_mut_str())
            } else {
                unreachable!("cow isn't owned after making it owned, what happened?")
            }
        }
        #[cfg(not(feature = "alloc"))]
        TriCow::Borrowed(_) => Err(Error::AllocRequired),
        TriCow::MutBorrowed(s) => Ok(s),
    }
}

pub fn make_uppercase<R>(c: &mut TriCow, range: R) -> Result<()>
where
    R: Clone + SliceIndex<str, Output = str>,
{
    if c[range.clone()].bytes().any(|b| b.is_ascii_lowercase()) {
        cow_mut_ref(c)?[range].make_ascii_uppercase();
    }
    Ok(())
}

pub fn make_lowercase<R>(c: &mut TriCow, range: R) -> Result<()>
where
    R: Clone + SliceIndex<str, Output = str>,
{
    if c[range.clone()].bytes().any(|b| b.is_ascii_uppercase()) {
        cow_mut_ref(c)?[range].make_ascii_lowercase();
    }
    Ok(())
}
