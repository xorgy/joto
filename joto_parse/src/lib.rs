// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Light-weight unit parsing of dimension strings into iota.
//!
//! `joto_parse` is intended to offer parsing functions that cover all common dimension parsing needs
//! for typesetting, for architectural and mechanical specification, or for general engineering use.
//! The functions herein can be evaluated in const contexts.
//! They do not panic, they do not allocate, and generally finish parsing in under 50 ns on a laptop.
//!
//! Intended for dimensioning, not for expressing ‘distances’ like an interplanetary voyage.
//! That having been said, in [`mod@i64`], the most restrictive supported integer unit, lengths
//! just over 1 Gm (1,000,000 km) can be represented in iota.
//! For reference, 1 Gm is more than twice the distance from the center of Earth to the farthest
//! the far side of the moon gets in orbit.
//! In [`mod@f64`], with 53 mantissa bits, lengths up to 1,000 km can be represented in exact iota.
//!
//! Both of the 128-bit integer types support truly absurd linear distances; in practice I expect
//! [`mod@i128`] and [`mod@u128`] to be used for area, up to around 2.1/4.2 × 10¹² km²,
//! and volume up to around 233/466 × 10⁶ m³ respectively.
//!
//! ## Examples
//!
//! ### Basic usage
//! ```
//! use joto_constants::length::u64::{FOOT, INCH, MILLIMETER, SIXTY_FOURTH};
//! use joto_parse::u64::parse_dim;
//!
//! assert_eq!(parse_dim("2.5cm").unwrap(), 25 * MILLIMETER);
//! assert_eq!(parse_dim("46'11 37⁄64\"").unwrap(), 46 * FOOT + 11 * INCH + 37 * SIXTY_FOURTH);
//! ```
//!
//! ### Invertibility
//!
//! Invertibility is the primary attraction of iota as a base unit.
//! You can add and subtract mixed units with iota, and by extension joto, without loss.
//!
//! ```
//! use joto_parse::u128::parse_dim;
//!
//! fn p(s: impl AsRef<str>) -> u128 {
//!     parse_dim(s.as_ref()).unwrap()
//! }
//!
//! assert_eq!(0, p("2.5cm") + p("1⁄64in") + p("0.500 in") - p("37,700μm") - p("1/64″"));
//! ```
//!
//! ### Constant evaluation
//!
//! The parsing functions are all `const`, so can be used for compile-time constants and statics.
//!
//! ```
//! use joto_parse::u128::parse_dim;
//! use joto_constants::length::u128::{FOOT, INCH, MILLIMETER, SIXTY_FOURTH};
//!
//! const DIAMETER: u128 = parse_dim("21ft11﻿17⁄32in").unwrap();
//! assert_eq!(DIAMETER / 2, 10 * FOOT + 11 * INCH + 49 * SIXTY_FOURTH);
//! ```
//!
//! Since parsing can be done at compile time, it can also fail at compile time.
//! This example fails to compile because 0.1 nm is too precise to represent:
//! ```compile_fail
//! use joto_parse::f64::parse_dim;
//! const FAIL: f64 = parse_dim("0.1 nm").unwrap();
//! ```

#![no_std]

use core::str;

use joto_constants::length::u64::{
    CENTIMETER, DECIMETER, FOOT, INCH, IOTA, METER, MICROMETER, MILLIMETER, NANOMETER, PICA, POINT,
    QUARTER_MILLIMETER, YARD,
};

/// Unit type for parsing.
///
/// These are distinct from the constants in [`joto_constants`] in the sense that they
/// are meant to represent parsing/generating behavior, and not numeric behavior.
#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
#[repr(u64)]
pub enum Unit {
    /// Iota ― one ninth of a nanometer.
    ///
    /// This allows common fractions of an inch ([`TEN_THOUSANDTH`], [`POINT`], [`SIXTY_FOURTH`])
    /// and [`NANOMETER`] to be represented as integers.
    /// Using this base unit, combinations of lengths in either [US customary Units] or [SI units]
    /// can be added, subtracted, multiplied, and sometimes divided without loss of precision.
    ///
    /// See [`IOTA`](joto_constants::length::u128::IOTA).
    ///
    /// [`TEN_THOUSANDTH`]: joto_constants::length::u128::TEN_THOUSANDTH
    /// [`POINT`]: joto_constants::length::u128::POINT
    /// [`SIXTY_FOURTH`]: joto_constants::length::u128::SIXTY_FOURTH
    /// [`NANOMETER`]: joto_constants::length::u128::NANOMETER
    ///
    /// [US customary Units]: <https://en.wikipedia.org/wiki/United_States_customary_units>
    /// [SI units]: <https://en.wikipedia.org/wiki/International_System_of_Units>
    Iota = IOTA,
    /// Inch ― exactly 1⁄12 of a [`Foot`](Unit::Foot).
    ///
    /// See [`INCH`](joto_constants::length::u128::INCH) in [`joto_constants`].
    ///
    /// [`FOOT`]: joto_constants::length::u128::FOOT
    Inch = INCH,
    /// Foot ― exactly 1⁄3 of a [`Yard`](Unit::Yard).
    ///
    /// See [`FOOT`](joto_constants::length::u128::FOOT) in [`joto_constants`].
    Foot = FOOT,
    /// Yard ― defined in the [International Yard and Pound agreement].
    ///
    /// See [`YARD`](joto_constants::length::u128::YARD) in [`joto_constants`].
    ///
    /// [International Yard and Pound agreement]: <https://en.wikipedia.org/wiki/International_yard_and_pound>
    Yard = YARD,
    /// [Desktop publishing point] ― exactly 1⁄72 of an [`Inch`] or 1⁄12 of a [`Pica`].
    ///
    /// See [`POINT`](joto_constants::length::u128::POINT) in [`joto_constants`].
    ///
    /// [`Inch`]: Unit::Inch
    /// [`Pica`]: Unit::Pica
    /// [desktop publishing point]: <https://en.wikipedia.org/wiki/Point_(typography)#Desktop_publishing_point>
    Point = POINT,
    /// Desktop Publishing Pica ― exactly 1⁄6 of an [`Inch`] or 12 [`Point`].
    ///
    /// See [`PICA`](joto_constants::length::u128::PICA) in [`joto_constants`].
    ///
    /// [`Inch`]: Unit::Inch
    /// [`Point`]: Unit::Point
    Pica = PICA,
    /// Nanometer.
    ///
    /// See [`NANOMETER`](joto_constants::length::u128::NANOMETER) in [`joto_constants`].
    Nanometer = NANOMETER,
    /// Micrometer.
    ///
    /// See [`MICROMETER`](joto_constants::length::u128::MICROMETER) in [`joto_constants`].
    Micrometer = MICROMETER,
    /// Millimeter.
    ///
    /// See [`MILLIMETER`](joto_constants::length::u128::MILLIMETER) in [`joto_constants`].
    Millimeter = MILLIMETER,
    /// Centimeter.
    ///
    /// See [`CENTIMETER`](joto_constants::length::u128::CENTIMETER) in [`joto_constants`].
    Centimeter = CENTIMETER,
    /// Decimeter.
    ///
    /// See [`DECIMETER`](joto_constants::length::u128::DECIMETER) in [`joto_constants`].
    Decimeter = DECIMETER,
    /// Meter.
    ///
    /// See [`METER`](joto_constants::length::u128::METER) in [`joto_constants`].
    Meter = METER,
    /// Q ― quarter-millimeter.
    ///
    /// This is a typesetting unit primarily used in Japan, equaling exactly 250 µm.
    ///
    /// See [`QUARTER_MILLIMETER`](joto_constants::length::u128::QUARTER_MILLIMETER) in
    /// [`joto_constants`].
    Q = QUARTER_MILLIMETER,
    //
    //    ATTENTION:
    //
    //       If you intend to add to this enumeration, make sure you recompute
    //       `unit_phf` and adjust `phf_match_unit_const_map` to match the order.
    //
    //
}

/// Perfect hash function for [`Unit`].
///
/// Because [`Unit`] is the value of the unit, and the units range from quite small to rather large,
/// a normal `match` on these values produces around 300 bytes of machine code.
///
/// Use of this hash with the `phf_match_unit_const_map` macro leads to significant performance
/// improvement for most opt levels, especially for `s` and `z` (between 10% and 25% faster).
#[inline(always)]
const fn unit_phf(u: Unit) -> u8 {
    (((u as u64).wrapping_mul(2962150912u64) >> 32) & 15) as u8
}

/// Produce a switch table for a [`Unit`] const function, indexed with [`unit_phf`].
macro_rules! phf_match_unit_const_map {
    (
        $(#[$outer:meta])*
        $VIS:vis const fn $NAME:ident : $FN:ident -> $TARGET:ty
    ) => {
        $(#[$outer])*
        $VIS const fn $NAME(unit: Unit) -> $TARGET {
            use Unit::*;
            match unit_phf(unit) {
                0 => const { $FN(Iota) },
                14 => const { $FN(Inch) },
                13 => const { $FN(Foot) },
                9 => const { $FN(Yard) },
                4 => const { $FN(Point) },
                5 => const { $FN(Pica) },
                6 => const { $FN(Nanometer) },
                15 => const { $FN(Micrometer) },
                11 => const { $FN(Millimeter) },
                3 => const { $FN(Centimeter) },
                1 => const { $FN(Decimeter) },
                10 => const { $FN(Meter) },
                2 => const { $FN(Q) },
                // SAFETY: `Unit` is a closed set, only the values above are reachable.
                _ => unsafe { ::core::hint::unreachable_unchecked() },
            }
        }
    };
}

/// Calculate the value of the least significant decimal fraction digit for a given unit.
const fn unit_lsd_inner(unit: Unit) -> u32 {
    let max_dgt = unit.max_decimal_digits() as u32;
    if max_dgt == 0 {
        // Normally some units would overflow u32, but
        // those are all divisible by many decimal places.
        unit as u32
    } else {
        (unit as u64 / 10u64.pow(max_dgt)) as u32
    }
}

phf_match_unit_const_map! {
    /// The base to use when parsing the least significant safe decimal digit.
    #[inline(always)]
    const fn unit_lsd : unit_lsd_inner -> u32
}

/// Maximum number of decimal fraction digits that are exactly represented in iota.
const fn max_decimal_digits_inner(u: Unit) -> u8 {
    use Unit::*;
    match u {
        Inch => 5,
        Meter => 9,
        Decimeter => 8,
        Centimeter => 7,
        Millimeter => 6,
        Micrometer => 3,
        Point => 3,
        Pica => 5,
        Q => 4,
        Yard => 5,
        Foot => 5,
        _ => 0,
    }
}

phf_match_unit_const_map! {
    /// The base to use when parsing the least significant safe decimal digit.
    #[inline(always)]
    const fn max_decimal_digits : max_decimal_digits_inner -> u8
}

impl Unit {
    /// Canonical abbreviation for unit.
    pub const fn abbr(self) -> &'static str {
        use Unit::*;
        match self {
            Iota => "io",
            Foot => "′",
            Inch => "″",
            Yard => "yd",
            Point => "pt",
            Pica => "pc",
            Nanometer => "nm",
            Micrometer => "µm",
            Millimeter => "mm",
            Centimeter => "cm",
            Decimeter => "dm",
            Meter => "m",
            Q => "Q",
        }
    }

    /// `true` if the unit is a standard SI unit ― i.e. not including [`Q`](Unit::Q).
    #[inline]
    pub const fn is_si(self) -> bool {
        use Unit::*;
        matches!(
            self,
            Nanometer | Micrometer | Millimeter | Centimeter | Decimeter | Meter
        )
    }

    /// `Some(Unit)` If `u` has a unit that it is sometimes its superior.
    ///
    /// Useful for formatting dimensions in a system that uses mixed units, and also for
    /// parsing mixed unit dimensions in that system.
    ///
    /// For example, if you have a dimension string that ends with inches, and there's more
    /// string before that, there's a good chance that there is a quantity in feet (the inch's
    /// superior) which is part of the same dimension.
    ///
    /// The other way around, when formatting a result that would be a very large number
    /// of inches, it is often preferable to use feet for the larger portion of the dimension.
    #[inline]
    pub const fn superior(self) -> Option<Unit> {
        if matches!(self, Unit::Inch) {
            Some(Unit::Foot)
        } else {
            None
        }
    }

    /// `Some(Unit)` If `u` has a unit that it is sometimes its inferior.
    ///
    /// Useful for formatting dimensions in a system that uses mixed units.
    ///
    /// For example, if you have a quantity in whole feet, and you do an operation on it and
    /// end up with a fraction, you should generally try to use inches to resolve it, then try
    /// whole number fractions of an inch, and then try decimal inches down to the 100,000th.
    #[inline]
    pub const fn inferior(self) -> Option<Unit> {
        if matches!(self, Unit::Foot) {
            Some(Unit::Inch)
        } else {
            None
        }
    }

    /// Maximum number of decimal fraction digits that are exactly represented in iota.
    ///
    /// Keep in mind that while it is safe to parse these units to this precision,
    /// it is not always customary to do so.
    ///
    /// When outputting a fraction for a unit, you should first consider whether
    /// it has a common [`inferior`](Unit::inferior), and then also if the given
    /// fraction is better represented as a whole number fraction than a decimal.
    #[inline]
    pub const fn max_decimal_digits(self) -> u8 {
        max_decimal_digits(self)
    }

    /// The base to use when parsing the least significant safe decimal digit.
    #[inline]
    pub const fn least_significant_digit_value(self) -> u32 {
        unit_lsd(self)
    }
}

/// Detect a unit at the end of a dimension string, returning the rest of the `str` and the [`Unit`].
// There are simpler ways to do this normally, but those are not available in a `const`
// context.
pub const fn strip_unit(s: &str) -> Option<(&str, Unit)> {
    let b = s.as_bytes();
    const fn bs(r: &[u8]) -> &str {
        // SAFETY: `r` is a prefix slice of `s` which is valid UTF-8 by construction.
        // Since our suffix patterns are all complete UTF-8 sequences or plain ASCII
        // bytes, they naturally fall on valid char boundaries.
        unsafe { str::from_utf8_unchecked(r) }
    }
    Some(match b {
        [r @ .., b'"'] |
        [r @ .., b'i', b'n'] |
        [r @ .., 0xE2, 0x80, 0xB3] // U+2033 Double Prime
            => (bs(r), Unit::Inch),

        [r @ .., b'\''] |
        [r @ .., b'f', b't'] |
        [r @ .., 0xE2, 0x80, 0xB2] // U+2032 Prime
            => (bs(r), Unit::Foot),

        [r @ .., b'y', b'd']  => (bs(r), Unit::Yard),

        [r @ .., b'n', b'm'] => (bs(r), Unit::Nanometer),

        [r @ .., b'u', b'm'] |
        [r @ .., 0xC2, 0xB5, b'm'] | // U+00B5 Micro Sign
        [r @ .., 0xCE, 0xBC, b'm']   // U+03BC Greek Small Letter Mu
            => (bs(r), Unit::Micrometer),

        [r @ .., b'm', b'm'] => (bs(r), Unit::Millimeter),

        [r @ .., b'c', b'm'] => (bs(r), Unit::Centimeter),

        [r @ .., b'd', b'm'] => (bs(r), Unit::Decimeter),

        [r @ .., b'm'] => (bs(r), Unit::Meter),

        [r @ .., b'Q'] => (bs(r), Unit::Q),

        [r @ .., b'p', b't']  => (bs(r), Unit::Point),

        [r @ .., b'p', b'c'] => (bs(r), Unit::Pica),

        [r @ .., b'i', b'o'] => (bs(r), Unit::Iota),

        _ => {return None},
    })
}

/// Return the string slice less whitespace at the end.
// Normal [`str::trim`] is not available in `const`, so this is necessary.
#[inline]
const fn trim_end(s: &str) -> &str {
    let mut rest = s.as_bytes();
    //  (U+202F | U+2009 | U+2000..=U+200B)
    // | U+FEFF
    // | U+00A0
    // | U+0020
    while let [r @ .., b' ']
    | [r @ .., 0xE2, 0x80, 0xAF | 0x80..=0x8B]
    | [r @ .., 0xEF, 0xBB, 0xBF]
    | [r @ .., 0xC2, 0xA0] = rest
    {
        rest = r;
    }
    // SAFETY: Original str was valid, and codepoint boundaries are preserved above.
    unsafe { str::from_utf8_unchecked(rest) }
}

/// Return the string slice less zeroes at the end.
// Normal [`str::strip_suffix`] is not available in `const`, so this is necessary.
#[inline]
const fn trim_trailing_zeroes(s: &str) -> &str {
    let mut rest = s.as_bytes();
    while let [r @ .., b'0'] = rest {
        rest = r;
    }
    // SAFETY: Original str was valid, and codepoint boundaries are preserved above.
    unsafe { str::from_utf8_unchecked(rest) }
}

/// Strip ASCII digits from the end of a str, returning slices split at the first non-digit.
// Normal functions for this are not available in `const`, so this is necessary.
#[inline]
const fn strip_digits(s: &str) -> (&str, &str) {
    let mut rest = s.as_bytes();
    while let [r @ .., b'0'..=b'9'] = rest {
        rest = r;
    }
    // SAFETY: rest.len() naturally falls on a char boundary, since it is the beginning
    //         of the last ASCII digit that matched at the end of a valid UTF-8 string.
    let (_, stripped) = unsafe { s.as_bytes().split_at_unchecked(rest.len()) };
    // SAFETY: Since str was valid UTF-8, and rest.len() is a valid boundary,
    //         `rest` and `stripped` are known to be valid UTF-8.
    unsafe {
        (
            str::from_utf8_unchecked(rest),
            str::from_utf8_unchecked(stripped),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ParseError {
    /// Empty or entirely whitespace.
    Empty,
    /// Missing or invalid unit.
    NoUnit {
        /// The point in the string where the issue was encountered.
        at: usize,
    },
    /// Missing quantity portion of the dimension.
    EmptyQuantity {
        /// The unit for which the quantity was expected.
        unit: Unit,
        /// The point in the string where the issue was encountered.
        at: usize,
    },
    /// Quantity is too large for unit.
    TooBig {
        /// The unit for which the quantity was too large.
        unit: Unit,
        /// The point in the string where the issue was encountered.
        at: usize,
    },
    /// Quantity is too precise for unit.
    TooPrecise {
        /// The unit for which the quantity was too precise.
        unit: Unit,
        /// The point in the string where the issue was encountered.
        at: usize,
    },
    /// Denominator in fraction is not accepted for unit.
    BadDenominator {
        /// The unit for which the denominator was invalid.
        unit: Unit,
        /// The point in the string where the issue was encountered.
        at: usize,
    },
    /// Numerator is out of range for unit or denominator.
    BadNumerator {
        /// The unit for which the numerator was invalid.
        unit: Unit,
        /// The point in the string where the issue was encountered.
        at: usize,
    },
    /// Found compound unit, but the superior unit was not valid for the inferior.
    InvalidCompound {
        /// The [inferior unit](Unit::inferior) in the compound.
        inferior: Unit,
        /// The unit that was found instead of the expected [superior](Unit::superior).
        found: Unit,
        /// The point in the string where the issue was encountered.
        at: usize,
    },
}

impl Unit {
    /// Parse a decimal fraction.
    #[inline]
    const fn take_decimal_frac(self, rest: &str) -> Result<(&str, i64), ParseError> {
        let unit = self;
        let at = rest.len();
        if let [r @ .., b'.'] = rest.as_bytes() {
            return if let [.., b'0'..=b'9'] = r {
                // No fraction, rest is a whole.
                // SAFETY: `r` ends on the char boundary of an ASCII digit.
                Ok((unsafe { str::from_utf8_unchecked(r) }, 0))
            } else {
                Err(ParseError::EmptyQuantity { unit, at })
            };
        }
        let (d_rest, digits) = strip_digits(rest);
        if d_rest.is_empty() {
            return Ok((rest, 0));
        }
        let nonzero_digits = trim_trailing_zeroes(digits);
        let len = nonzero_digits.len();
        let [r @ .., b'.'] = d_rest.as_bytes() else {
            return Ok((rest, 0));
        };
        // SAFETY: `r` always ends on the char boundary of `b'.'`.
        let rest = unsafe { str::from_utf8_unchecked(r) };
        if len == 0 {
            return if !rest.is_empty() || !digits.is_empty() {
                Ok((rest, 0))
            } else {
                Err(ParseError::EmptyQuantity { unit, at })
            };
        }
        let scale = unit.max_decimal_digits() as usize;
        if len > scale {
            return Err(ParseError::TooPrecise { unit, at });
        }
        let b = nonzero_digits.as_bytes();
        let len = b.len();
        let mut pv = unit_lsd(unit) as i64;
        let mut acc = 0i64;
        let mut i = scale;
        while i > len {
            i -= 1;
            // SAFETY: initial `pv` is `unit / 10.powi(scale)`, so this can't overflow.
            pv = unsafe { pv.unchecked_mul(10) };
        }
        while i > 0 {
            i -= 1;
            // SAFETY: initial `pv` is `unit / 10.powi(scale)`, so none of these can overflow.
            unsafe {
                let d = b[i] & 0xF;
                let dv = (d as i64).unchecked_mul(pv);
                acc = acc.unchecked_add(dv);
                pv = pv.unchecked_mul(10);
            }
        }
        Ok((rest, acc))
    }
}

/// Parse and validate an inch denominator, and return the quantity of 1 over itself.
#[inline]
const fn parse_inch_denom_pv(s: &str) -> Option<(u32, u32)> {
    const INCH: u32 = Unit::Inch as u32;
    Some(match s.as_bytes() {
        b"2" => (2, const { INCH / 2 }),
        b"4" => (4, const { INCH / 4 }),
        b"8" => (8, const { INCH / 8 }),
        b"16" => (16, const { INCH / 16 }),
        b"32" => (32, const { INCH / 32 }),
        b"64" => (64, const { INCH / 64 }),
        _ => {
            return None;
        }
    })
}

/// Parse a numerator for a proper fraction of an inch.
///
/// We do not currently support improper fractions, so numerators are one or two digits.
///
/// # Safety
/// Caller is responsible for ensuring `s` is one or two ASCII digits.
#[inline]
const unsafe fn parse_inch_num(s: &str) -> Option<u32> {
    Some(match s.as_bytes() {
        [ones] => (*ones & 0xF) as u32,
        [tens, ones] => {
            let tens = (*tens & 0xF) as u32;
            let ones = (*ones & 0xF) as u32;
            // SAFETY: This can't overflow.
            unsafe { tens.unchecked_mul(10).unchecked_add(ones) }
        }
        _ => {
            return None;
        }
    })
}

/// Parse an inch fraction.
#[inline]
const fn take_inch_frac(rest: &str) -> Result<(&str, u32), ParseError> {
    let at = rest.len();
    let unit = Unit::Inch;
    let (d_rest, denom_digits) = strip_digits(rest);
    if denom_digits.is_empty() {
        return Err(ParseError::EmptyQuantity { unit, at });
    }
    match d_rest.as_bytes() {
        [r @ .., b'/'] |
        // U+2044 FRACTION SLASH
        [r @ .., 0xE2, 0x81, 0x84] => {
            let Some((den, den_pv)) = parse_inch_denom_pv(denom_digits)
            else {
                return Err(ParseError::BadDenominator { unit, at });
            };
            // SAFETY: `r` ranges from the beginning of a valid UTF-8 string to
            //         a valid char boundary for `b'/'` or U+2044.
            let s = unsafe { str::from_utf8_unchecked(r) };
            let at = s.len();
            let (rest, numerator_digits) = strip_digits(s);

            if numerator_digits.is_empty() {
                return Err(ParseError::BadNumerator { unit, at });
            }
            // SAFETY: `numerator_digits` stripped as ASCII digits.
            let Some(num_v) = (unsafe { parse_inch_num(numerator_digits) }) else {
                return Err(ParseError::BadNumerator { unit, at });
            };
            if num_v >= den || num_v < 1 {
                return Err(ParseError::BadNumerator { unit, at });
            }
            // SAFETY: Domains of `den_pv` and `num_v` can't overflow in mul.
            let acc = unsafe { (den_pv).unchecked_mul(num_v) };
            Ok((trim_end(rest), acc))
        }
        [r @ .., b'.'] => {
            let scale = unit.max_decimal_digits() as usize;
            // SAFETY: `r` ranges from the beginning of a valid UTF-8 string,
            //         to a valid char boundary for `b'.'`.
            let rest = unsafe { str::from_utf8_unchecked(r)};
            let at = rest.len();
            let digits = trim_trailing_zeroes(denom_digits);
            let len = digits.len();
            if len == 0 {
                Ok((rest, 0))
            } else if len > scale {
                Err(ParseError::TooPrecise { unit, at })
            } else {
                let b = digits.as_bytes();
                // `u32` is large enough for any fraction of an inch.
                let mut pv = unit_lsd(unit);
                let mut i = scale;
                while i > len {
                    i -= 1;
                    // SAFETY: `i` is bounded so `pv` never exceeds `INCH`, and `INCH < u32::MAX`.
                    pv = unsafe { pv.unchecked_mul(10) };
                }
                let mut acc = 0u32;
                while i > 0 {
                    i -= 1;
                    // SAFETY: `i` and `pv` inherently fit in `u32`, so none of these can overflow.
                    unsafe {
                        let d =  b[i] & 0xF;
                        let dv = (d as u32).unchecked_mul(pv);
                        acc = acc.unchecked_add(dv);
                        pv = pv.unchecked_mul(10);
                    }
                }
                Ok((rest, acc))
            }
        }
        _ => Ok((rest, 0))
    }
}

macro_rules! typed_mod {
    ( $T:ident ) => {
        /// Parsing functions for dimensions.
        pub mod $T {
            use super::*;

            type Target = $T;

            const fn max_whole_place_inner(unit: Unit) -> u8 {
                (Target::MAX / unit as Target).ilog10() as u8
            }

            phf_match_unit_const_map! {
                /// Maximum whole decimal place where at least digit 1 fits `Target` for `unit`.
                ///
                /// This perfect hash function cuts the compiled size of [`parse_whole_diagnostic`]
                /// in half by compressing the information in the unit constants to fit in a small
                /// immediate.
                #[inline(always)]
                const fn max_whole_place : max_whole_place_inner -> u8
            }

            /// Accumulate the maximum digit from the string.
            ///
            /// This is rare so doesn't warrant inlining.
            const fn accum_max_digit(
                unit: Unit,
                acc: Target,
                pv: Target,
                rest: &str,
            ) -> Result<(&str, Target), ParseError> {
                let mut acc = acc;
                let mut rest = rest.as_bytes();
                if let [r @ .., c @ b'0'..=b'9'] = rest {
                    let at = rest.len();
                    rest = r;
                    // SAFETY: Overflow impossible for source types.
                    let v = unsafe { (*c as u32).unchecked_sub(b'0' as u32) };
                    let Some(mv) = pv.checked_mul(v as Target) else {
                        return Err(ParseError::TooBig { unit, at });
                    };
                    let Some(na) = acc.checked_add(mv) else {
                        return Err(ParseError::TooBig { unit, at });
                    };
                    acc = na;
                }

                loop {
                    while let [r @ .., b'0'] = rest {
                        rest = r;
                    }

                    // Strip one comma or U+2028 Punctuation Space.
                    if let [r @ .., b','] | [r @ .., 0xE2, 0x80, 0x88] = rest {
                        rest = r;
                    } else {
                        break;
                    }
                }

                if let [.., b'1'..=b'9'] = rest {
                    return Err(ParseError::TooBig {
                        unit,
                        at: rest.len(),
                    });
                }

                Ok((unsafe { str::from_utf8_unchecked(rest) }, acc))
            }

            /// Parse a whole number string, returning the digit that causes an overflow as [`Err`].
            ///
            /// The content is known to be only ASCII digits and commas.
            #[inline]
            const fn parse_whole_diagnostic(
                unit: Unit,
                acc: Target,
                s: &str,
            ) -> Result<(&str, Target), ParseError> {
                let mut pv = unit as Target;
                let mut acc = acc;
                let max_place = max_whole_place(unit);
                let mut p = 0;
                let mut rest = s.as_bytes();
                let [.., b'0'..=b'9'] = rest else {
                    return Err(ParseError::EmptyQuantity {
                        unit,
                        at: rest.len(),
                    });
                };

                'parse: loop {
                    while let [r @ .., c @ b'0'..=b'9'] = rest {
                        if p < max_place {
                            let at = rest.len();
                            rest = r;
                            // SAFETY: Overflow impossible for source types.
                            let v = unsafe { (*c as u32).unchecked_sub(b'0' as u32) };
                            // SAFETY: Proven safe by `p < max_place`, since `v <= 9`.
                            let mv = unsafe { pv.unchecked_mul(v as Target) };
                            let Some(na) = acc.checked_add(mv) else {
                                return Err(ParseError::TooBig { unit, at });
                            };
                            acc = na;
                            // SAFETY: Proven safe by `p < max_place`.
                            pv = unsafe { pv.unchecked_mul(10) };
                            p += 1;
                        } else {
                            break 'parse;
                        }
                    }

                    // Strip one comma or U+2028 Punctuation Space.
                    if let [r @ .., b','] | [r @ .., 0xE2, 0x80, 0x88] = rest {
                        rest = r;
                    } else {
                        break;
                    }
                }

                // SAFETY: `s` was valid UTF-8, and rest ends on a valid boundary.
                let rest = unsafe { str::from_utf8_unchecked(rest) };

                if p != max_place {
                    Ok((rest, acc))
                } else {
                    accum_max_digit(unit, acc, pv, rest)
                }
            }

            /// Parse a dimension string, returning a [`ParseError`] if parsing fails.
            #[inline]
            pub const fn parse_dim_diagnostic(s: &str) -> Result<Target, ParseError> {
                let rest = trim_end(s);
                if rest.is_empty() {
                    return Err(ParseError::Empty);
                }
                let at = rest.len();
                if let Some((rest, unit)) = strip_unit(rest) {
                    let at = rest.len();
                    let rest = trim_end(rest);
                    if !rest.is_empty() {
                        let (rest, acc) = match unit {
                            Unit::Inch => match take_inch_frac(rest) {
                                Ok((rest, v)) => (rest, v as Target),
                                Err(e) => return Err(e),
                            },
                            _ => match unit.take_decimal_frac(rest) {
                                Ok((rest, v)) if !rest.is_empty() => (rest, v as Target),
                                Ok((_, v)) => {
                                    return Ok(v as Target);
                                }
                                Err(e) => {
                                    return Err(e);
                                }
                            },
                        };
                        let (rest, acc) = match parse_whole_diagnostic(unit, acc, rest) {
                            Ok((rest, acc)) => (rest, acc),
                            Err(ParseError::EmptyQuantity { .. }) if acc != 0 => {
                                return Ok(acc);
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        };

                        if let Some(sup) = unit.superior() {
                            let rest = trim_end(rest);
                            let at = rest.len();
                            // Check unit ourselves.
                            if let Some((rest, next_unit)) = strip_unit(rest) {
                                if next_unit as u64 == sup as u64 {
                                    return match parse_whole_diagnostic(sup, acc, trim_end(rest)) {
                                        Ok((_, acc)) => Ok(acc),
                                        Err(e) => Err(e),
                                    };
                                } else {
                                    return Err(ParseError::InvalidCompound {
                                        inferior: unit,
                                        found: next_unit,
                                        at,
                                    });
                                }
                            }
                        }
                        Ok(acc)
                    } else {
                        Err(ParseError::EmptyQuantity { unit, at })
                    }
                } else {
                    Err(ParseError::NoUnit { at })
                }
            }

            /// Parse a dimension string, returning [`None`] if there is an error.
            ///
            /// See [`parse_dim_diagnostic`] for information on how to handle errors.
            #[inline]
            pub const fn parse_dim(s: &str) -> Option<Target> {
                match parse_dim_diagnostic(s) {
                    Ok(v) => Some(v),
                    _ => None,
                }
            }
        }
    };
}

typed_mod!(u64);
typed_mod!(i64);
typed_mod!(u128);
typed_mod!(i128);

/// Parsing functions for dimensions.
pub mod f64 {
    use super::u64::parse_dim as parse_dim_u64;
    use super::u64::parse_dim_diagnostic as parse_dim_diagnostic_u64;
    use super::{strip_unit, trim_end, ParseError};

    /// Maximum contiguous `f64`-safe integer.
    const MAX_SAFE: u64 = 1 << f64::MANTISSA_DIGITS;

    /// Parse a dimension string, returning a [`ParseError`] if parsing fails.
    #[inline]
    pub const fn parse_dim_diagnostic(s: &str) -> Result<f64, ParseError> {
        match parse_dim_diagnostic_u64(s) {
            Ok(ui) => {
                if ui <= MAX_SAFE {
                    Ok(ui as f64)
                } else {
                    let Some((r, unit)) = strip_unit(trim_end(s)) else {
                        unreachable!();
                    };
                    Err(ParseError::TooBig { at: r.len(), unit })
                }
            }
            Err(e) => Err(e),
        }
    }

    /// Parse a dimension string, returning [`None`] if there is an error.
    ///
    /// See [`parse_dim_diagnostic`] for information on how to handle errors.
    pub const fn parse_dim(s: &str) -> Option<f64> {
        match parse_dim_u64(s) {
            Some(ui) if (ui <= MAX_SAFE) => Some(ui as f64),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {

    macro_rules! test_submod {
        ( $T:ident ) => {
            #[cfg(test)]
            mod $T {
                use super::super::$T::*;
                use super::super::{ParseError, Unit};

                type Target = $T;

                use joto_constants::length::$T::{
                    CENTIMETER, DECIMETER, FOOT, HUNDRED_THOUSANDTH, INCH, METER, MICROMETER,
                    MILLIMETER, NANOMETER, PICA, POINT, QUARTER, SIXTY_FOURTH,
                };

                /// Const panic wrapper for [`parse_dim`] for better feedback.
                const fn p(s: &str) -> Target {
                    parse_dim(s).unwrap()
                }

                #[test]
                fn invertibility_sanity_check() {
                    const V: Target =
                        p("2.5cm") + p("1⁄64in") + p("1⁄2 in") - p("37,700μm") - p("1/64\"");
                    assert_eq!(0, V)
                }

                #[test]
                fn basic_parse_dim() {
                    assert_eq!(p("37'"), 37 * FOOT);
                    assert_eq!(p("11\""), 11 * INCH);
                }

                #[test]
                fn compound_parse_dim() {
                    assert_eq!(p("37'11\""), 37 * FOOT + 11 * INCH);
                    assert_eq!(p("37'11 1⁄4\""), 37 * FOOT + 11 * INCH + 1 * QUARTER);
                }

                #[test]
                fn with_decimal_parse_dim() {
                    assert_eq!(p(".00001\""), HUNDRED_THOUSANDTH);
                    assert_eq!(
                        p("37'11.00039\""),
                        37 * FOOT + 11 * INCH + 39 * HUNDRED_THOUSANDTH
                    );
                    assert_eq!(p("37'11.1\""), 37 * FOOT + 11 * INCH + INCH / 10);
                }

                #[test]
                fn si_whole_parse_dim() {
                    assert_eq!(p("1nm"), NANOMETER);
                    assert_eq!(p("1um"), MICROMETER);
                    assert_eq!(p("1µm"), MICROMETER);
                    assert_eq!(p("1Q"), MILLIMETER / 4);
                    assert_eq!(p("1mm"), MILLIMETER);
                    assert_eq!(p("1cm"), CENTIMETER);
                    assert_eq!(p("1dm"), DECIMETER);
                    assert_eq!(p("1m"), METER);
                    assert_eq!(p(" 1 nm "), NANOMETER);
                    assert_eq!(p(" 1 um "), MICROMETER);
                    assert_eq!(p(" 1 µm "), MICROMETER);
                    assert_eq!(p(" 1 Q "), MILLIMETER / 4);
                    assert_eq!(p(" 1 mm "), MILLIMETER);
                    assert_eq!(p(" 1 cm "), CENTIMETER);
                    assert_eq!(p(" 1 dm "), DECIMETER);
                    assert_eq!(p(" 1 m "), METER);
                }

                #[test]
                fn si_decimal_parse_dim() {
                    assert_eq!(const { p(".0nm") }, 0);
                    assert_eq!(parse_dim(".1nm"), None);
                    assert_eq!(const { p(".000nm") }, 0);
                    assert_eq!(parse_dim(".0001nm"), None);

                    assert_eq!(const { p(".0um") }, 0);
                    assert_eq!(const { p(".001um") }, NANOMETER);
                    assert_eq!(parse_dim(".0001um"), None);
                    assert_eq!(const { p(".0000um") }, 0);

                    // U+00B5
                    assert_eq!(const { p(".0µm") }, 0);
                    assert_eq!(const { p(".001µm") }, NANOMETER);
                    assert_eq!(parse_dim(".0001µm"), None);
                    assert_eq!(const { p(".0000µm") }, 0);

                    // U+03BC
                    assert_eq!(const { p(".0μm") }, 0);
                    assert_eq!(const { p(".001μm") }, NANOMETER);
                    assert_eq!(parse_dim(".0001μm"), None);
                    assert_eq!(const { p(".0000μm") }, 0);

                    assert_eq!(const { p(".0Q") }, 0);
                    assert_eq!(const { p(".0001Q") }, 25 * NANOMETER);
                    assert_eq!(parse_dim(".000004Q"), None);
                    assert_eq!(const { p(".0000000Q") }, 0);

                    assert_eq!(const { p(".0mm") }, 0);
                    assert_eq!(const { p(".000001mm") }, NANOMETER);
                    assert_eq!(parse_dim(".0000001mm"), None);
                    assert_eq!(const { p(".0000000mm") }, 0);

                    assert_eq!(const { p(".0cm") }, 0);
                    assert_eq!(const { p(".0000001cm") }, NANOMETER);
                    assert_eq!(parse_dim(".00000001cm"), None);
                    assert_eq!(const { p(".0000000cm") }, 0);

                    assert_eq!(const { p(".0dm") }, 0);
                    assert_eq!(const { p(".00000001dm") }, NANOMETER);
                    assert_eq!(parse_dim(".000000001dm"), None);
                    assert_eq!(const { p(".00000000dm") }, 0);

                    assert_eq!(const { p(".0m") }, 0);
                    assert_eq!(const { p(".000000001m") }, NANOMETER);
                    assert_eq!(parse_dim(".0000000001m"), None);
                    assert_eq!(const { p(".000000000m") }, 0);
                }

                #[test]
                fn si_with_decimal_parse_dim() {
                    assert_eq!(p("1.0nm"), NANOMETER);
                    assert_eq!(p("1.000nm"), NANOMETER);

                    assert_eq!(p("2.001um"), 2 * MICROMETER + NANOMETER);
                    assert_eq!(p("2.000um"), 2 * MICROMETER);

                    assert_eq!(p("3.000001mm"), 3 * MILLIMETER + NANOMETER);
                    assert_eq!(p("3.000000mm"), 3 * MILLIMETER);

                    assert_eq!(p("4.0000001cm"), 4 * CENTIMETER + NANOMETER);
                    assert_eq!(p("4.0000000cm"), 4 * CENTIMETER);

                    assert_eq!(p("5.00000001dm"), 5 * DECIMETER + NANOMETER);
                    assert_eq!(p("5.00000000dm"), 5 * DECIMETER);

                    assert_eq!(p("6.000000001m"), 6 * METER + NANOMETER);
                    assert_eq!(p("6.000000000m"), 6 * METER);
                }

                #[test]
                fn compound_funk() {
                    const R: &str = "  34,966' 11 1⁄4\"  ";
                    assert_eq!(p(R), 34_966 * FOOT + 11 * INCH + 1 * QUARTER);

                    const S: &str = "  34,966' 11﻿1⁄4\"  ";
                    assert_eq!(p(S), 34_966 * FOOT + 11 * INCH + 1 * QUARTER);

                    const P: &str = "  34,966  ' 11﻿1⁄4\"  ";
                    assert_eq!(p(P), 34_966 * FOOT + 11 * INCH + 1 * QUARTER);
                }

                #[test]
                fn whole_picas_parse_dim() {
                    const R5PC: Target = p("5pc");
                    assert_eq!(R5PC, 5 * PICA);
                    const R1PC: Target = p("1pc");
                    assert_eq!(R1PC, 1 * PICA);
                    const R10MPC: Target = p("10,000,000 pc");
                    assert_eq!(R10MPC, 10_000_000 * PICA);
                }

                #[test]
                fn whole_points_parse_dim() {
                    const R5PT: Target = p("5pt");
                    assert_eq!(R5PT, 5 * POINT);
                    const R1PT: Target = p("1pt");
                    assert_eq!(R1PT, 1 * POINT);
                    const R10MPT: Target = p("10,000,000 pt");
                    assert_eq!(R10MPT, 10_000_000 * POINT);
                }

                #[test]
                fn assorted_whitespace() {
                    const W1: Target = p("320,333\u{00A0}\u{FEFF}\u{2009}\u{200A}\u{202f}\u{2033}");
                    assert_eq!(W1, 320_333 * INCH);
                    const W2: Target = p("\u{2005}﻿17⁄32\u{2000}″\u{2001}\u{2002}\u{2003}\u{2004}");
                    assert_eq!(W2, 34 * SIXTY_FOURTH);
                    const W3: Target = p("\u{2006}﻿3⁄8\u{2007}″\u{2008}\u{2009}\u{200A}\u{200B}");
                    assert_eq!(W3, 24 * SIXTY_FOURTH);
                }

                #[test]
                fn grouping_separators() {
                    // Make sure we accept U+2008 Punctuation Space as a whole group separator.
                    const G1: Target = p("67\u{2008}000,000\u{2008}000\u{202f}io");
                    assert_eq!(G1, 67_000_000_000);
                }

                #[test]
                fn parse_diagnostics() {
                    extern crate alloc;
                    use alloc::format;

                    const P1: Target = p("69in");
                    assert_eq!(P1, INCH * 69);
                    const P2: Target = p("21'11\"");
                    assert_eq!(P2, FOOT * 21 + INCH * 11);
                    const P3: Target = p("21'11﻿37⁄64\"");
                    assert_eq!(P3, FOOT * 21 + INCH * 11 + 37 * SIXTY_FOURTH);
                    const P4: Target = p("21'11.25000000\"");
                    assert_eq!(P4, FOOT * 21 + INCH * 11 + 1 * QUARTER);
                    const P5: Target = p("9.0000 nm");
                    assert_eq!(P5, 9 * NANOMETER);
                    const P6: Target = p("9 nm");
                    assert_eq!(P6, 9 * NANOMETER);
                    const P7: Result<Target, ParseError> = parse_dim_diagnostic("9.1 nm");
                    assert_eq!(
                        P7,
                        Err(ParseError::TooPrecise {
                            unit: Unit::Nanometer,
                            at: 3
                        })
                    );
                    const P8: Target = p("5mm");
                    assert_eq!(P8, 5 * MILLIMETER);
                    const P9: Target = p("5.0mm");
                    assert_eq!(P9, 5 * MILLIMETER);
                    const P10: Target = p("0.5cm");
                    assert_eq!(P10, 5 * MILLIMETER);
                    const P11: Target = p("2.5cm");
                    assert_eq!(P11, 25 * MILLIMETER);
                    const P12: Result<Target, ParseError> = parse_dim_diagnostic("nm");
                    assert_eq!(
                        P12,
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Nanometer,
                            at: 0
                        })
                    );
                    const P13: Target = p("0nm");
                    assert_eq!(P13, 0);
                    const P14: Result<Target, ParseError> = parse_dim_diagnostic("nm");
                    assert_eq!(
                        P14,
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Nanometer,
                            at: 0
                        })
                    );
                    const P15: Result<Target, ParseError> = parse_dim_diagnostic("39");
                    assert_eq!(P15, Err(ParseError::NoUnit { at: 2 }));
                    const P16: Result<Target, ParseError> = parse_dim_diagnostic("");
                    assert_eq!(P16, Err(ParseError::Empty));
                    let p17: Result<Target, ParseError> =
                        parse_dim_diagnostic(format!("{}nm", (Target::MAX / 9) + 1).as_ref());
                    assert_eq!(
                        p17,
                        Err(ParseError::TooBig {
                            unit: Unit::Nanometer,
                            at: 1
                        })
                    );
                    let p18: Target = p(format!("{}io", Target::MAX).as_ref());
                    assert_eq!(p18, Target::MAX);

                    // Empty: entirely whitespace
                    const P19: Result<Target, ParseError> = parse_dim_diagnostic("   ");
                    assert_eq!(P19, Err(ParseError::Empty));

                    // NoUnit: invalid unit suffix
                    const P20: Result<Target, ParseError> = parse_dim_diagnostic("1foo");
                    assert_eq!(P20, Err(ParseError::NoUnit { at: 4 }));

                    // EmptyQuantity: whitespace before unit
                    const P21: Result<Target, ParseError> = parse_dim_diagnostic(" mm ");
                    assert_eq!(
                        P21,
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Millimeter,
                            at: 1
                        })
                    );

                    // TooPrecise: too many decimal digits for unit
                    const P22: Result<Target, ParseError> = parse_dim_diagnostic("1.0000001mm");
                    assert_eq!(
                        P22,
                        Err(ParseError::TooPrecise {
                            unit: Unit::Millimeter,
                            at: 9
                        })
                    );

                    // BadDenominator: denominator not a power of 2 for inch
                    const P23: Result<Target, ParseError> = parse_dim_diagnostic("1/3\"");
                    assert_eq!(
                        P23,
                        Err(ParseError::BadDenominator {
                            unit: Unit::Inch,
                            at: 3
                        })
                    );

                    // BadNumerator: numerator >= denominator
                    const P24: Result<Target, ParseError> = parse_dim_diagnostic("3/2\"");
                    assert_eq!(
                        P24,
                        Err(ParseError::BadNumerator {
                            unit: Unit::Inch,
                            at: 1
                        })
                    );

                    // BadNumerator: zero numerator
                    const P25: Result<Target, ParseError> = parse_dim_diagnostic("0/2\"");
                    assert_eq!(
                        P25,
                        Err(ParseError::BadNumerator {
                            unit: Unit::Inch,
                            at: 1
                        })
                    );

                    // InvalidCompound: superior unit does not match expected for inferior
                    let p26: Result<Target, ParseError> = parse_dim_diagnostic("1m1\"");
                    assert_eq!(
                        p26,
                        Err(ParseError::InvalidCompound {
                            inferior: Unit::Inch,
                            found: Unit::Meter,
                            at: 2
                        })
                    );

                    let digits = (Target::MAX.ilog10() as usize) + 1;

                    // Overflows when advancing the whole number place value.
                    let p27_str = format!("1{}io", "0".repeat(digits));
                    let p27: Result<Target, ParseError> = parse_dim_diagnostic(&p27_str);
                    assert_eq!(
                        p27,
                        Err(ParseError::TooBig {
                            unit: Unit::Iota,
                            at: 1
                        })
                    );

                    // Overflows when adding the place value to the accumulator.
                    let p28_str = format!("1{}io", "9".repeat(digits));
                    let p28: Result<Target, ParseError> = parse_dim_diagnostic(&p28_str);
                    assert_eq!(
                        p28,
                        Err(ParseError::TooBig {
                            unit: Unit::Iota,
                            at: 2
                        })
                    );

                    // Overflows when multiplying the place value with the digit.
                    let p29_str = format!("9{}io", "0".repeat(digits));
                    let p29: Result<Target, ParseError> = parse_dim_diagnostic(&p29_str);
                    assert_eq!(
                        p29,
                        Err(ParseError::TooBig {
                            unit: Unit::Iota,
                            at: 1
                        })
                    );
                }
            }
        };
    }

    test_submod!(u64);
    test_submod!(i64);
    test_submod!(u128);
    test_submod!(i128);

    mod f64 {
        use super::super::f64::parse_dim;
        use joto_constants::length::f64::{QUARTER, SIXTY_FOURTH};

        #[test]
        fn parse_sanity() {
            assert_eq!(parse_dim("1⁄4in").unwrap(), QUARTER);
            assert_eq!(parse_dim("1⁄64in").unwrap(), SIXTY_FOURTH);
            assert_eq!(parse_dim("37⁄64in").unwrap(), 37. * SIXTY_FOURTH);
        }

        #[test]
        fn parse_check_overflow() {
            extern crate alloc;
            use alloc::format;
            assert_eq!(
                parse_dim(format!("{}io", (1u64 << f64::MANTISSA_DIGITS) + 1).as_ref()),
                None
            );
        }
    }

    #[test]
    fn basic_trim_end() {
        assert_eq!(super::trim_end("foo  \u{202F} "), "foo");
    }
}
