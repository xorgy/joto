<div align=center>

# Joto Workspace

**¿por que no los dos?**

[![dependency status](https://deps.rs/repo/github/xorgy/joto/status.svg)](https://deps.rs/repo/github/xorgy/joto)
[![ISC/MIT/Apache 2.0](https://img.shields.io/badge/license-ISC%2FMIT%2FApache-blue.svg)](#license)
[![Build status](https://github.com/xorgy/joto/workflows/CI/badge.svg)](https://github.com/xorgy/joto/actions)
[![Crates.io](https://img.shields.io/crates/v/joto.svg)](https://crates.io/crates/joto)
[![Docs](https://docs.rs/joto/badge.svg)](https://docs.rs/joto)

</div>

This workspace is a collection of constants and tools for interoperating US Customary and SI units of length/displacement, with a focus on avoiding unnecessary loss of precision and idempotency.

In the `joto_constants` package, `IOTA` is defined as one ninth of a nanometer.
This allows common fractions of an inch (ten-thousandths, desktop publishing points, and sixty-fourths) and nanometers to be represented as integers.
Using this base unit, combinations of lengths in either [US customary units](<https://en.wikipedia.org/wiki/United_States_customary_units>) or [SI units](<https://en.wikipedia.org/wiki/International_System_of_Units>) can be added, subtracted, and multiplied without loss of precision.

## Minimum Supported Rust Version (MSRV)

These packages have been verified to compile with **Rust 1.64** and later.

Future versions might increase the Rust version requirement.
It will not be treated as a breaking change, and as such can even happen with small patch releases.

## License

Licensed under

- ISC license
   ([LICENSE-ISC](LICENSE-ISC))
- Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
- MIT license
   ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contribution

Contributions are welcome by pull request.
Please feel free to add your name to the [AUTHORS] file in any substantive pull request.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in th ework by you, as defined in the Apache-2.0 license, shall be
licensed above, without any additional terms or conditions.

[AUTHORS]: ./AUTHORS
