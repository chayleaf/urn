[![crates.io](https://img.shields.io/crates/v/urn.svg)](https://crates.io/crates/urn) [![docs.rs](https://docs.rs/urn/badge.svg)](https://docs.rs/urn)

# URN

A Rust crate for handling [URNs](https://datatracker.ietf.org/doc/html/rfc8141). Parsing and comparison is done according to the spec (meaning only part of the URN is used for equality checks). `no_std` support is available if you disable the default "std" feature. `alloc` is needed, but the `Urn` type is a wrapper around `String` and should only use a single allocation (but I haven't checked). You can even construct a `Urn` from your own `String` by using `TryFrom<String>`, that way it shouldn't allocate at all.

## Changelog

- 0.1.0 - initial release
- 0.1.1 - add FromStr impl
- 0.2.0 - remove Urn::parse function in favor of FromStr, improve docs
- 0.2.1 - remove files left over from 0.1
- 0.3.0 - major implementation changes, remove `Namespace` (thanks to u/chris-morgan for help)
- 0.3.1 - fix a panic on empty NSS and add `?=` terminator to r-component (both `?` and `=` can be part of r-component, but together they terminate it)
- 0.3.2 - add `Clone` impl for `Urn`

## License

TL;DR do whatever you want.

Licensed under either the [BSD Zero Clause License](LICENSE-0BSD) (https://opensource.org/licenses/0BSD), the [Apache 2.0 License](LICENSE-APACHE) (http://www.apache.org/licenses/LICENSE-2.0) or the [MIT License](LICENSE-MIT) (http://opensource.org/licenses/MIT), at your choice.

