//! A crate for handling [URNs](https://datatracker.ietf.org/doc/html/rfc8141).
#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::{borrow::{Cow, ToOwned}, fmt, string::String};
use core::{convert::TryFrom, result};
use displaydoc::Display;
#[cfg(feature = "std")]
use std::{borrow::Cow, fmt};

include!(concat!(env!("OUT_DIR"), "/generated.rs"));

impl TryFrom<&str> for Namespace {
    type Error = Error;
    fn try_from(s: &str) -> Result<Self> {
        Self::new(s)
    }
}

impl TryFrom<String> for Namespace {
    type Error = Error;
    fn try_from(s: String) -> Result<Self> {
        Self::new(&s)
    }
}

fn eat_tag<'a, 'b>(s: &'a str, tag: &'b str) -> Option<&'a str> {
    if s.len() >= tag.len() && (&s[..tag.len()]).to_ascii_lowercase() == tag {
        Some(&s[tag.len()..])
    } else {
        None
    }
}

fn parse_nid(s: &str) -> Result<(Namespace, &str)> {
    if s.len() >= 2 && !s.starts_with('-') {
        let (nid, rest) = s
            .bytes()
            .enumerate()
            .find(|(_, c)| (*c as char) != '-' && !(*c as char).is_ascii_alphanumeric())
            .map_or_else(|| (s, &s[s.len()..]), |(i, _)| (&s[..i], &s[i..]));
        Ok((Namespace::new(nid)?, rest))
    } else {
        Err(Error::InvalidNid)
    }
}

fn is_valid_nid(s: &str) -> bool {
    if let Ok((_, s)) = parse_nid(s) {
        s.is_empty()
    } else {
        false
    }
}

fn valid_percent_to_upper(s: &str) -> String {
    let mut ret = String::new();
    let mut it = s.bytes().enumerate();
    while let Some((i, c)) = it.next() {
        match c as char {
            '%' if s
                .bytes()
                .skip(i + 1)
                .take(2)
                .any(|b| (b as char).is_ascii_lowercase()) =>
            {
                ret.push('%');
                ret.push((it.next().unwrap().1 as char).to_ascii_uppercase());
                ret.push((it.next().unwrap().1 as char).to_ascii_uppercase());
            }
            c => ret.push(c),
        }
    }
    ret
}

fn parse_encoded(
    s: &str,
    can_start_with_slash: bool,
    with_qmark: bool,
) -> Option<(Cow<str>, &str)> {
    let mut it = s.bytes().enumerate();
    let mut needs_up = false;
    while let Some((i, c)) = it.next() {
        match c as char {
            '?' if with_qmark => {}
            c if c.is_ascii_alphanumeric() => {}
            '/' if i == 0 && can_start_with_slash => {}
            '/' if i != 0 => {}
            '-' | '.' | '_' | '~' | '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';'
            | '=' | ':' | '@' => {}
            '%' if i + 2 < s.len()
                && s.bytes()
                    .skip(i + 1)
                    .take(2)
                    .all(|b| (b as char).is_ascii_hexdigit()) =>
            {
                if !needs_up
                    && s.bytes()
                        .skip(i + 1)
                        .take(2)
                        .any(|b| (b as char).is_ascii_lowercase())
                {
                    needs_up = true;
                }
                it.next();
                it.next();
            }
            _ => {
                return if needs_up {
                    Some((valid_percent_to_upper(&s[..i]).into(), &s[i..]))
                } else {
                    Some(((&s[..i]).into(), &s[i..]))
                };
            }
        }
    }
    if needs_up {
        Some((valid_percent_to_upper(&s[..s.len()]).into(), &s[s.len()..]))
    } else {
        Some(((&s[..s.len()]).into(), &s[s.len()..]))
    }
}

fn parse_nss(s: &str) -> Result<(Cow<str>, &str)> {
    if let Some((a, b)) = parse_encoded(s, false, false) {
        if a.len() > 0 {
            return Ok((a, b));
        }
    }
    Err(Error::InvalidNss)
}

fn parse_rq_component(s: &str) -> Result<(Cow<str>, &str)> {
    if let Some((a, b)) = parse_encoded(s, false, true) {
        if a.len() > 0 {
            return Ok((a, b));
        }
    }
    Err(Error::InvalidRComponent)
}

fn parse_f_component(s: &str) -> Result<(Cow<str>, &str)> {
    if let Some((a, b)) = parse_encoded(s, true, true) {
        return Ok((a, b));
    }
    Err(Error::InvalidFComponent)
}

fn parse_urn(s: &str) -> Result<Urn> {
    let s = eat_tag(s, "urn:").ok_or(Error::InvalidScheme)?;
    let (ns, s) = parse_nid(s)?;
    if s.is_empty() {
        return Err(Error::InvalidNss);
    }
    let s = eat_tag(s, ":").ok_or(Error::InvalidNid)?;
    let (nss, mut s) = parse_nss(s)?;
    let mut builder = UrnBuilder::new(ns, &nss);
    let mut leftover_error = Error::InvalidNss;
    if let Some(t) = eat_tag(s, "?+") {
        let (rc, t) = parse_rq_component(t)?;
        builder = builder.r_component(&rc);
        s = t;
        leftover_error = Error::InvalidRComponent;
    }
    if let Some(t) = eat_tag(s, "?=") {
        let (qc, t) = parse_rq_component(t)?;
        builder = builder.q_component(&qc);
        s = t;
        leftover_error = Error::InvalidQComponent;
    }
    if let Some(t) = eat_tag(s, "#") {
        let (fc, t) = parse_f_component(t)?;
        builder = builder.f_component(&fc);
        s = t;
        leftover_error = Error::InvalidFComponent;
    }
    if !s.is_empty() {
        return Err(leftover_error);
    }
    builder.build()
}

#[derive(Debug, Display)]
pub enum Error {
    /// invalid urn scheme
    InvalidScheme,
    /// invalid urn namespace identifier
    InvalidNid,
    /// invalid urn namespace-specific string
    InvalidNss,
    /// invalid urn r-component (resolve info)
    InvalidRComponent,
    /// invalid urn q-component (query)
    InvalidQComponent,
    /// invalid urn f-component (fragment)
    InvalidFComponent,
}

type Result<T> = result::Result<T, Error>;

#[cfg(feature = "std")]
impl std::error::Error for Error {}

#[derive(Debug)]
pub struct Urn {
    /// NID, namespace identifier
    namespace: Namespace,
    /// NSS, namespace-specific string
    nss: String,
    r_component: Option<String>,
    q_component: Option<String>,
    f_component: Option<String>,
}

impl Urn {
    pub fn parse(urn: &str) -> Result<Self> {
        parse_urn(urn)
    }
    /// NID (Namespace identifier), the first part of the URN.
    /// For example, in `urn:ietf:rfc:2648`, `ietf` is the namespace.
    /// In this crate, it would be defined as [`Namespace::Ietf`].
    pub fn namespace(&self) -> &Namespace {
        &self.namespace
    }
    pub fn set_namespace(&mut self, namespace: Namespace) -> Result<()> {
        self.namespace = namespace;
        Ok(())
    }
    /// NSS (Namespace-specific string) identifying the resource.
    /// For example, in `urn:ietf:rfc:2648`, `rfs:2648` is the NSS.
    pub fn nss(&self) -> &str {
        &self.nss
    }
    pub fn set_nss(&mut self, nss: &str) -> Result<()> {
        let (nss, s) = parse_nss(nss)?;
        if !s.is_empty() {
            return Err(Error::InvalidNss);
        }
        self.nss = nss.into();
        Ok(())
    }
    /// r-component, following the `?+` character sequence, to be used for passing parameters
    /// to URN resolution services.
    /// In `urn:example:foo-bar-baz-qux?+CCResolve:cc=uk`, `CCResolve:cc=uk` is the r-component.
    /// Should not be used for equivalence checks. As of 2021, exact semantics are undefined.
    pub fn r_component(&self) -> Option<&str> {
        self.r_component.as_deref()
    }
    pub fn set_r_component(&mut self, r_component: Option<&str>) -> Result<()> {
        if let Some(rc) = r_component {
            let (rc, s) = parse_rq_component(rc)?;
            if !s.is_empty() {
                return Err(Error::InvalidRComponent);
            }
            self.r_component = Some(rc.into());
        } else {
            self.r_component = None;
        }
        Ok(())
    }
    /// q-component, following the `?=` character sequence. Used for querying the resource.
    /// Should not be used for equivalence checks.
    pub fn q_component(&self) -> Option<&str> {
        self.q_component.as_deref()
    }
    pub fn set_q_component(&mut self, q_component: Option<&str>) -> Result<()> {
        if let Some(qc) = q_component {
            let (qc, s) = parse_rq_component(qc)?;
            if !s.is_empty() {
                return Err(Error::InvalidQComponent);
            }
            self.q_component = Some(qc.into());
        } else {
            self.q_component = None;
        }
        Ok(())
    }
    /// f-component (fragment) following the # character.
    /// Should not be used for equivalence checks.
    pub fn f_component(&self) -> Option<&str> {
        self.f_component.as_deref()
    }
    pub fn set_f_component(&mut self, f_component: Option<&str>) -> Result<()> {
        if let Some(fc) = f_component {
            let (fc, s) = parse_f_component(fc)?;
            if !s.is_empty() {
                return Err(Error::InvalidFComponent);
            }
            self.f_component = Some(fc.into());
        } else {
            self.f_component = None;
        }
        Ok(())
    }
}

impl PartialEq for Urn {
    fn eq(&self, other: &Self) -> bool {
        self.namespace == other.namespace && self.nss == other.nss
    }
}

impl Eq for Urn {}

impl fmt::Display for Urn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> result::Result<(), fmt::Error> {
        write!(f, "urn:{}:{}", self.namespace(), self.nss())?;
        if let Some(rc) = self.r_component() {
            write!(f, "?+{}", rc)?;
        }
        if let Some(qc) = self.q_component() {
            write!(f, "?={}", qc)?;
        }
        if let Some(fc) = self.f_component() {
            write!(f, "#{}", fc)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct UrnBuilder {
    /// NID, namespace identifier
    namespace: Namespace,
    /// NSS, namespace-specific string
    nss: String,
    r_component: Option<String>,
    q_component: Option<String>,
    f_component: Option<String>,
}

impl UrnBuilder {
    pub fn new(namespace: Namespace, nss: &str) -> Self {
        Self {
            namespace,
            nss: nss.to_owned(),
            r_component: None,
            q_component: None,
            f_component: None,
        }
    }
    pub fn namespace(mut self, namespace: Namespace) -> Self {
        self.namespace = namespace;
        self
    }
    pub fn nss(mut self, nss: &str) -> Self {
        self.nss = nss.to_owned();
        self
    }
    pub fn r_component(mut self, r_component: &str) -> Self {
        self.r_component = Some(r_component.to_owned());
        self
    }
    pub fn q_component(mut self, q_component: &str) -> Self {
        self.q_component = Some(q_component.to_owned());
        self
    }
    pub fn f_component(mut self, f_component: &str) -> Self {
        self.f_component = Some(f_component.to_owned());
        self
    }

    pub fn build(self) -> Result<Urn> {
        let (nss, s) = parse_nss(&self.nss)?;
        if !s.is_empty() {
            return Err(Error::InvalidNss);
        }
        let mut ret = Urn {
            namespace: self.namespace,
            nss: nss.into(),
            r_component: None,
            q_component: None,
            f_component: None,
        };
        ret.set_r_component(self.r_component.as_deref())?;
        ret.set_q_component(self.q_component.as_deref())?;
        ret.set_f_component(self.f_component.as_deref())?;
        Ok(ret)
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
            Urn::parse("urn:nbn:de:bvb:19-146642").unwrap(),
            UrnBuilder::new(Namespace::Nbn, "de:bvb:19-146642")
                .build()
                .unwrap()
        );
        assert_eq!(
            Urn::parse("urn:nbn:de:bvb:19-146642").unwrap().to_string(),
            "urn:nbn:de:bvb:19-146642"
        );

        assert_eq!(
            Urn::parse("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test").unwrap(),
            UrnBuilder::new(Namespace::Example, "foo-bar-baz-qux")
                .r_component("CCResolve:cc=uk")
                .f_component("test")
                .build()
                .unwrap()
        );
        assert_eq!(
            Urn::parse("urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test").unwrap().to_string(),
            "urn:example:foo-bar-baz-qux?+CCResolve:cc=uk#test",
        );

        assert_eq!(
            Urn::parse(
                "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
            )
            .unwrap(),
            UrnBuilder::new(Namespace::Example, "weather")
                .q_component("op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z")
                .build()
                .unwrap()
        );
        assert_eq!(
            Urn::parse(
                "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
            ).unwrap().to_string(),
            "urn:example:weather?=op=map&lat=39.56&lon=-104.85&datetime=1969-07-21T02:56:15Z"
        );

        assert_eq!(
            Urn::parse("uRn:eXaMpLe:%3d%3a?=aoiwnfuafo").unwrap(),
            UrnBuilder::new(Namespace::Example, "%3D%3a")
                .build()
                .unwrap()
        );
        assert_eq!(
            Urn::parse("uRn:eXaMpLe:%3d%3a?=aoiwnfuafo").unwrap().to_string(),
            "urn:example:%3D%3A?=aoiwnfuafo",
        );
    }
}
