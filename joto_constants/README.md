<div align=center>

# Joto Constants

**Real interoperability since 1959!**

[![dependency status](https://deps.rs/repo/github/xorgy/joto/status.svg)](<https://deps.rs/repo/github/xorgy/joto>)
[![ISC/MIT/Apache 2.0](https://img.shields.io/badge/license-ISC%2FMIT%2FApache-blue.svg)](#license)
[![Build status](https://github.com/xorgy/joto/workflows/CI/badge.svg)](<https://github.com/xorgy/joto/actions>)
[![Crates.io](https://img.shields.io/crates/v/joto_constants.svg)](<https://crates.io/crates/joto_constants>)
[![Docs](https://docs.rs/joto_constants/badge.svg)](<https://docs.rs/joto_constants>)

</div>

## Operating principle

Here we set out to interoperate US Customary and SI units of length/displacement, mass, and temperature, while preserving invertibility, avoiding uncontrolled precision loss, and replacing structured unit types ― which are tricky to store or compute efficiently ― with plain integers.

This is accomplished by defining common base units for length, mass, and temperature, which can be used to express [US customary units](<https://en.wikipedia.org/wiki/United_States_customary_units>) and [SI units](<https://en.wikipedia.org/wiki/International_System_of_Units>) in the same scale for each domain.

### Length/displacement

For length, there is the *iota*, defined as 1⁄9 nm.

This allows common fractions of an inch (ten-thousandths, desktop publishing points, and sixty-fourths) and multiples of the nanometer to be represented as natural numbers.

### Mass

For mass, there is the *whit*, defined as 1⁄3200 µg.

The whit is chosen to express practically measurable weights (down to the 0.1 µg range) as well as all common fractional denominations of the international pound (ounces, dram, thousandths of an ounce, grains) and units related to the pound by grains (such as the troy ounce).

### Temperature

For temperature, there is the *smidge*, defined as 1⁄90 mK.

The smidge represents temperatures down to the 100 µK/0.0001 °R range, which is sufficient for almost all practical thermometry. This also allows you to exactly represent temperatures used in industrial metrology standards such as [ITS-90](<https://en.wikipedia.org/wiki/International_Temperature_Scale_of_1990>) for fixed points and common derived constants, and allows exact interchange between common absolute (Kelvin/[Rankine](<https://en.wikipedia.org/wiki/Rankine_scale>)) and relative (Celsius/Fahrenheit) temperature scales.

The `temperature` module deliberately avoids defining incremental units of temperature by their relative scale names, to remind users to account for the difference in origin/zero point between Fahrenheit and Celsius.

## Minimum Supported Rust Version (MSRV)

This version of `joto_constants` has been verified to compile with **Rust 1.64** and later.

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
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
licensed above, without any additional terms or conditions.

[AUTHORS]: ../AUTHORS
