[![crates.io](https://img.shields.io/crates/v/urn.svg)](https://crates.io/crates/urn) [![docs.rs](https://docs.rs/urn/badge.svg)](https://docs.rs/urn)

# URN

A Rust crate for handling [URNs](https://datatracker.ietf.org/doc/html/rfc8141). Parsing and comparison is done according to the spec. no_std support is there as well, just disable the default "std" feature.

## Changelog

0.1.0 - initial release
0.1.1 - add FromStr impl
0.2.0 - remove Urn::parse function in favor of FromStr, improve docs
0.2.1 - remove files left over from 0.1
