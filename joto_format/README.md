<div align=center>

# Joto Format

**How do you write it down?**

[![dependency status](https://deps.rs/repo/github/xorgy/joto/status.svg)](<https://deps.rs/repo/github/xorgy/joto>)
[![ISC/MIT/Apache 2.0](https://img.shields.io/badge/license-ISC%2FMIT%2FApache-blue.svg)](#license)
[![Build status](https://github.com/xorgy/joto/workflows/CI/badge.svg)](<https://github.com/xorgy/joto/actions>)
[![Crates.io](https://img.shields.io/crates/v/joto_format.svg)](<https://crates.io/crates/joto_format>)
[![Docs](https://docs.rs/joto_format/badge.svg)](<https://docs.rs/joto_format>)

</div>

This package contains const-safe, allocation-free formatting of lengths, masses, and temperatures for working with other `joto` workspace packages.

In this workspace, `IOTA` is defined as one ninth of a nanometer, `WHIT` as 1⁄3200 µg, and `SMIDGE` as 1⁄90 mK.
Formatting uses these integer base units and displays them as mixed-unit strings with exactness tracking.

## Examples

### Basic usage
```rust
use joto_constants::length::u64::MILLIMETER;
use joto_format::length::u64::format_dim;
use joto_format::length::{LengthFormat, Unit};

let o = format_dim(12345 * MILLIMETER, Unit::Meter, LengthFormat::new());
assert_eq!(o.as_str(), "12.345m");
assert!(o.exact);
```

### Exactness

Formatting results include an `exact` field which indicates whether the value is exactly represented by the formatted string.

```rust
use joto_constants::mass::u64::MICROGRAM;
use joto_format::mass::u64::format_dim;
use joto_format::mass::{MassFormat, Unit};

let o = format_dim(MICROGRAM + MICROGRAM / 1000, Unit::Microgram, MassFormat::new());
assert_eq!(o.as_str(), "1µg");
assert!(!o.exact);
```

## Minimum Supported Rust Version (MSRV)

This version of `joto_format` has been verified to compile with **Rust 1.83** and later.

Future versions might increase the Rust version requirement.
It will not be treated as a breaking change, and as such can even happen with small patch releases.

## License

Triple licensed, at your option:

- ISC license
   ([LICENSE-ISC](LICENSE-ISC))
- Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license
   ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)


## Contribution

Contributions are welcome by pull request or email.
Please feel free to add your name to the [AUTHORS] file in any substantive pull request.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be licensed as above, without any additional terms or conditions.

[AUTHORS]: ./AUTHORS
