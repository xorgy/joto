<div align=center>

# Joto Parse

**What's in a number?**

[![dependency status](https://deps.rs/repo/github/xorgy/joto/status.svg)](<https://deps.rs/repo/github/xorgy/joto>)
[![ISC/MIT/Apache 2.0](https://img.shields.io/badge/license-ISC%2FMIT%2FApache-blue.svg)](#license)
[![Build status](https://github.com/xorgy/joto/workflows/CI/badge.svg)](<https://github.com/xorgy/joto/actions>)
[![Crates.io](https://img.shields.io/crates/v/joto_parse.svg)](<https://crates.io/crates/joto_parse>)
[![Docs](https://docs.rs/joto_parse/badge.svg)](<https://docs.rs/joto_parse>)

</div>

This package contains const-safe, allocation-free parsing of mixed units into iota for working with other `joto` workspace packages.

In this workspace, `IOTA` is defined as one ninth of a nanometer.
This allows common fractions of an inch (ten-thousandths, desktop publishing points, and sixty-fourths) and nanometers to be represented as integers.
Using this base unit, combinations of lengths in either [US customary units](<https://en.wikipedia.org/wiki/United_States_customary_units>) or [SI units](<https://en.wikipedia.org/wiki/International_System_of_Units>) can be added, subtracted, and multiplied without loss of precision.

## Examples

### Basic usage
```rust
use joto_constants::length::u64::{FOOT, INCH, MILLIMETER, SIXTY_FOURTH};
use joto_parse::length::u64::parse_dim;

assert_eq!(parse_dim("2.5cm").unwrap(), 25 * MILLIMETER);
assert_eq!(parse_dim("46'11﻿37⁄64\"").unwrap(), 46 * FOOT + 11 * INCH + 37 * SIXTY_FOURTH);
```

### Invertibility

Invertibility is the primary attraction of iota as a base unit.
You can add and subtract mixed units with iota, and by extension joto, without loss.

```rust
use joto_parse::length::u128::parse_dim;

fn p(s: impl AsRef<str>) -> u128 {
    parse_dim(s.as_ref()).unwrap()
}

assert_eq!(0, p("2.5cm") + p("1⁄64in") + p("0.500 in") - p("37,700μm") - p("1/64″"));
```

### Constant evaluation

The parsing functions are all `const`, so can be used for compile-time constants and statics.

```rust
use joto_parse::length::u128::parse_dim;
use joto_constants::length::u128::{FOOT, INCH, MILLIMETER, SIXTY_FOURTH};

const DIAMETER: u128 = parse_dim("21ft11﻿17⁄32in").unwrap();
assert_eq!(DIAMETER / 2, 10 * FOOT + 11 * INCH + 49 * SIXTY_FOURTH);
```


## Minimum Supported Rust Version (MSRV)

This version of `joto_parse` has been verified to compile with **Rust 1.79** and later.

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
