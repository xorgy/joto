// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Light-weight unit parsing of temperature strings into smidge.
//!
//! `joto_parse` is intended to offer parsing functions that cover all common dimension parsing
//! needs for typesetting, for architectural and mechanical specification, or for general
//! engineering use.
//! The functions herein can be evaluated in const contexts.
//! They do not panic, they do not allocate, and generally finish parsing in under 50 ns on a
//! laptop.
//!
//! In this workspace, [`SMIDGE`](joto_constants::temperature::u128::SMIDGE) is defined as 1⁄90 mK.
//! This allows exact interchange between common absolute (Kelvin/Rankine) and relative
//! (Celsius/Fahrenheit) temperature scales, while still representing very fine temperature
//! increments (0.1 mK/0.0001 °R).
//!
//! ## Examples
//! ```rust
//! use joto_constants::temperature::u32::{KELVIN, RANKINE, ZERO_CELSIUS, ZERO_FAHRENHEIT};
//! use joto_parse::temperature::u32::parse_dim;
//!
//! assert_eq!(parse_dim("373.15K").unwrap(), ZERO_CELSIUS + 100 * KELVIN);
//! assert_eq!(parse_dim("32°F").unwrap(), ZERO_FAHRENHEIT + 32 * RANKINE);
//! ```

use core::str;

use joto_constants::temperature::u32::{
    KELVIN, MILLIKELVIN, RANKINE, SMIDGE, THOUSANDTH_RANKINE, ZERO_CELSIUS, ZERO_FAHRENHEIT,
};

/// Unit type for parsing.
///
/// These are distinct from the constants in [`joto_constants`] in the sense that they
/// are meant to represent parsing/generating behavior, and not numeric behavior.
#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
pub enum Unit {
    /// Smidge ― 1⁄90 mK.
    Smidge,
    /// Millikelvin.
    Millikelvin,
    /// Kelvin ― absolute scale of Celsius.
    Kelvin,
    /// Thousandth rankine ― 0.001 °R.
    ThousandthRankine,
    /// Rankine ― absolute scale of Fahrenheit.
    Rankine,
    /// Celsius ― relative scale based on Kelvin, with origin at [`ZERO_CELSIUS`].
    ///
    /// Parsed values are absolute temperatures: `t°C = ZERO_CELSIUS + t × KELVIN`.
    Celsius,
    /// Fahrenheit ― relative scale based on Rankine, with origin at [`ZERO_FAHRENHEIT`].
    ///
    /// Parsed values are absolute temperatures: `t°F = ZERO_FAHRENHEIT + t × RANKINE`.
    Fahrenheit,
}

impl Unit {
    /// Canonical abbreviation for unit.
    pub const fn abbr(self) -> &'static str {
        use Unit::*;
        match self {
            Smidge => "sd",
            Millikelvin => "mK",
            Kelvin => "K",
            ThousandthRankine => "m°R",
            Rankine => "°R",
            Celsius => "°C",
            Fahrenheit => "°F",
        }
    }

    /// Canonical ASCII abbreviation for the unit.
    pub const fn ascii_abbr(self) -> &'static [u8] {
        use Unit::*;
        match self {
            Smidge => b"sd",
            Millikelvin => b"mK",
            Kelvin => b"K",
            ThousandthRankine => b"mR",
            Rankine => b"R",
            Celsius => b"C",
            Fahrenheit => b"F",
        }
    }

    /// `true` if the unit is a standard SI unit.
    #[inline]
    pub const fn is_si(self) -> bool {
        use Unit::*;
        matches!(self, Smidge | Millikelvin | Kelvin | Celsius)
    }

    /// Maximum number of decimal fraction digits that are exactly represented in smidge.
    #[inline]
    pub const fn max_decimal_digits(self) -> u8 {
        use Unit::*;
        match self {
            Smidge => 0,
            Millikelvin => 1,
            Kelvin => 4,
            ThousandthRankine => 1,
            Rankine => 4,
            Celsius => 4,
            Fahrenheit => 4,
        }
    }

    /// Unit increment in smidge.
    #[inline]
    pub const fn scale(self) -> u32 {
        use Unit::*;
        match self {
            Smidge => SMIDGE,
            Millikelvin => MILLIKELVIN,
            Kelvin | Celsius => KELVIN,
            ThousandthRankine => THOUSANDTH_RANKINE,
            Rankine | Fahrenheit => RANKINE,
        }
    }

    /// Unit origin offset in smidge.
    #[inline]
    pub const fn origin_offset(self) -> u32 {
        use Unit::*;
        match self {
            Celsius => ZERO_CELSIUS,
            Fahrenheit => ZERO_FAHRENHEIT,
            _ => 0,
        }
    }

    /// The base to use when parsing the least significant safe decimal digit.
    #[inline]
    pub const fn least_significant_digit_value(self) -> u32 {
        use Unit::*;
        match self {
            Smidge => SMIDGE,
            Millikelvin | Kelvin | Celsius => 9,
            ThousandthRankine | Rankine | Fahrenheit => 5,
        }
    }

    /// Parse a decimal fraction.
    #[inline]
    const fn take_decimal_frac(self, rest: &str) -> Result<(&str, u32, bool), ParseError> {
        let unit = self;
        let at = rest.len();
        if let [r @ .., b'.'] = rest.as_bytes() {
            return if let [.., b'0'..=b'9'] = r {
                // No fraction, rest is a whole.
                // SAFETY: `r` ends on the char boundary of an ASCII digit.
                Ok((unsafe { str::from_utf8_unchecked(r) }, 0u32, false))
            } else {
                Err(ParseError::EmptyQuantity { unit, at })
            };
        }
        let (d_rest, digits) = strip_digits(rest);
        if d_rest.is_empty() {
            return Ok((rest, 0, false));
        }
        let had_frac_digits = !digits.is_empty();
        let nonzero_digits = trim_trailing_zeroes(digits);
        let len = nonzero_digits.len();
        let [r @ .., b'.'] = d_rest.as_bytes() else {
            return Ok((rest, 0, false));
        };
        // SAFETY: `r` always ends on the char boundary of `b'.'`.
        let rest = unsafe { str::from_utf8_unchecked(r) };
        if len == 0 {
            return if !rest.is_empty() || !digits.is_empty() {
                Ok((rest, 0, had_frac_digits))
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
        let mut pv = unit.least_significant_digit_value();
        let mut acc = 0u32;
        let mut i = scale;
        while i > len {
            i -= 1;
            // SAFETY: `pv` is always <= unit.scale(), and unit scales fit in `u32`.
            pv = unsafe { pv.unchecked_mul(10) };
        }
        while i > 0 {
            i -= 1;
            // SAFETY: `pv` is always <= unit.scale(), and unit scales fit in `u32`.
            unsafe {
                let d = b[i] & 0xF;
                let dv = (d as u32).unchecked_mul(pv);
                acc = acc.unchecked_add(dv);
                pv = pv.unchecked_mul(10);
            }
        }
        Ok((rest, acc, true))
    }
}

/// Detect a unit at the end of a temperature string, returning the rest of the `str` and the
/// [`Unit`].
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
        // Smidge
        [r @ .., b's', b'd'] => (bs(r), Unit::Smidge),

        // Celsius / Fahrenheit (strip the degree sign if present)
        [r @ .., 0xC2, 0xB0, b'C'] | [r @ .., b'C'] => (bs(r), Unit::Celsius),
        [r @ .., 0xC2, 0xB0, b'F'] | [r @ .., b'F'] => (bs(r), Unit::Fahrenheit),

        // Millikelvin / Kelvin
        [r @ .., b'm', b'K'] => (bs(r), Unit::Millikelvin),
        [r @ .., b'K'] => (bs(r), Unit::Kelvin),

        // Thousandth rankine / Rankine (strip the degree sign if present)
        [r @ .., b'm', 0xC2, 0xB0, b'R'] | [r @ .., b'm', b'R'] => (bs(r), Unit::ThousandthRankine),
        [r @ .., 0xC2, 0xB0, b'R'] | [r @ .., b'R'] => (bs(r), Unit::Rankine),

        _ => {
            return None;
        }
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

/// Detect and strip a sign at the end of a string.
#[inline]
const fn strip_sign(s: &str) -> (&str, i8, bool) {
    let b = s.as_bytes();
    const fn bs(r: &[u8]) -> &str {
        // SAFETY: `r` is a prefix slice of `s` which is valid UTF-8 by construction.
        unsafe { str::from_utf8_unchecked(r) }
    }
    match b {
        [r @ .., b'+'] => (bs(r), 1, true),
        [r @ .., b'-'] => (bs(r), -1, true),
        // U+2212 MINUS SIGN
        [r @ .., 0xE2, 0x88, 0x92] => (bs(r), -1, true),
        _ => (s, 1, false),
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
    /// Missing quantity portion of the temperature.
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
    /// Quantity is too small for target type.
    TooSmall {
        /// The unit for which the quantity was too small.
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
    /// Found a sign where it is not valid for the given unit.
    InvalidSign {
        /// The unit for which the sign was invalid.
        unit: Unit,
        /// The point in the string where the issue was encountered.
        at: usize,
    },
}

macro_rules! typed_mod {
    ( $T:ident ) => {
        /// Parsing functions for temperature.
        pub mod $T {
            use super::*;

            type Target = $T;

            /// Parse a `°C` or `°F` quantity with `i32`-width arithmetic.
            ///
            /// Negative signs are handled by computing `origin - magnitude` in `i32`, which is
            /// equivalent to restarting the accumulation at the origin with negated place values.
            ///
            /// Returns [`None`] when the magnitude does not fit in `i32` and the caller should
            /// fall back to `Target` parsing.
            #[inline]
            const fn parse_relative_restart_i32(
                unit: Unit,
                s: &str,
                frac_u32: u32,
                had_frac: bool,
            ) -> Option<Result<Target, ParseError>> {
                // This path is only worthwhile for wide targets; narrow targets are already `i32`/`u32`
                // width and the generic parser is faster.
                if Target::BITS <= 32 {
                    return None;
                }
                if unit.origin_offset() == 0 {
                    return None;
                }

                let b = s.as_bytes();
                let has_whole = matches!(b, [.., b'0'..=b'9']);
                if !has_whole && !had_frac {
                    return Some(Err(ParseError::EmptyQuantity { unit, at: s.len() }));
                }

                let origin_u32 = unit.origin_offset();
                let origin_i32 = origin_u32 as i32;
                let frac_i32 = frac_u32 as i32;

                let (rest, mag_opt) = parse_whole_magnitude_i32(unit, frac_i32, s);
                let rest = trim_end(rest);
                let (rest, sign, has_sign) = strip_sign(rest);
                let at = rest.len();

                if has_sign && sign < 0 {
                    let Some(mag_i32) = mag_opt else {
                        return Some(Err(ParseError::TooSmall { unit, at }));
                    };
                    let abs_i32 = origin_i32 - mag_i32;
                    if abs_i32 >= 0 {
                        Some(Ok(abs_i32 as Target))
                    } else {
                        Some(Err(ParseError::TooSmall { unit, at }))
                    }
                } else {
                    let Some(mag_i32) = mag_opt else {
                        return None;
                    };
                    // Guaranteed not to overflow `u32`, since both `origin` and `magnitude` are
                    // known to be less than `i32::MAX` in smidge.
                    let abs_u32 = origin_u32 + mag_i32 as u32;
                    Some(Ok(abs_u32 as Target))
                }
            }

            /// Parse the `whole` portion of a `°C` or `°F` quantity into an `i32` magnitude in
            /// smidge, returning the remaining prefix and the accumulated magnitude.
            ///
            /// This always scans the entire number, but only computes the magnitude while it is
            /// known to fit in `i32`. After the place value exceeds the `i32` range, remaining
            /// digits must be zero for the magnitude to remain representable.
            #[inline]
            const fn parse_whole_magnitude_i32(
                unit: Unit,
                acc: i32,
                s: &str,
            ) -> (&str, Option<i32>) {
                let mut pv = unit.scale();
                let mut acc = acc;
                let mut acc_ok = true;
                let mut only_zeroes = false;
                let mut rest = s.as_bytes();

                'parse: loop {
                    while let [r @ .., c @ b'0'..=b'9'] = rest {
                        rest = r;
                        if acc_ok {
                            let d = ((*c) & 0xF) as i32;
                            if !only_zeroes {
                                if pv <= (i32::MAX as u32) / 9 {
                                    // SAFETY: `pv <= i32::MAX/9` and `d <= 9`.
                                    let dv = unsafe { d.unchecked_mul(pv as i32) };
                                    if let Some(na) = acc.checked_add(dv) {
                                        acc = na;
                                    } else {
                                        acc_ok = false;
                                    }
                                } else if d != 0 {
                                    acc_ok = false;
                                } else {
                                    only_zeroes = true;
                                }

                                if !only_zeroes {
                                    if let Some(npv) = pv.checked_mul(10) {
                                        pv = npv;
                                    } else {
                                        only_zeroes = true;
                                    }
                                }
                            } else if d != 0 {
                                acc_ok = false;
                            }
                        }
                    }

                    // Strip one comma or U+2028 Punctuation Space.
                    if let [r @ .., b','] | [r @ .., 0xE2, 0x80, 0x88] = rest {
                        rest = r;
                    } else {
                        break 'parse;
                    }
                }

                // SAFETY: `s` was valid UTF-8, and rest ends on a valid boundary.
                let rest = unsafe { str::from_utf8_unchecked(rest) };
                if acc_ok {
                    (rest, Some(acc))
                } else {
                    (rest, None)
                }
            }

            /// Maximum whole decimal place where at least digit 1 fits `Target` for `unit`.
            #[inline(always)]
            const fn max_whole_place(unit: Unit) -> u8 {
                use Unit::*;
                match unit {
                    Smidge => (Target::MAX / SMIDGE as Target).ilog10() as u8,
                    Millikelvin => (Target::MAX / MILLIKELVIN as Target).ilog10() as u8,
                    Kelvin | Celsius => (Target::MAX / KELVIN as Target).ilog10() as u8,
                    ThousandthRankine => {
                        (Target::MAX / THOUSANDTH_RANKINE as Target).ilog10() as u8
                    }
                    Rankine | Fahrenheit => (Target::MAX / RANKINE as Target).ilog10() as u8,
                }
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
                let mut pv = unit.scale() as Target;
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

            #[inline]
            const fn finalize(unit: Unit, acc: Target, rest: &str) -> Result<Target, ParseError> {
                let rest = trim_end(rest);
                let (rest, sign, has_sign) = strip_sign(rest);
                if has_sign && unit.origin_offset() == 0 {
                    return Err(ParseError::InvalidSign {
                        unit,
                        at: rest.len(),
                    });
                }

                let origin = unit.origin_offset() as Target;
                if has_sign && sign < 0 {
                    if acc > origin {
                        Err(ParseError::TooSmall {
                            unit,
                            at: rest.len(),
                        })
                    } else {
                        Ok(origin - acc)
                    }
                } else {
                    match origin.checked_add(acc) {
                        Some(v) => Ok(v),
                        None => Err(ParseError::TooBig {
                            unit,
                            at: rest.len(),
                        }),
                    }
                }
            }

            /// Parse a temperature string, returning a [`ParseError`] if parsing fails.
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
                        let (rest, frac_u32, had_frac) = match unit.take_decimal_frac(rest) {
                            Ok((rest, v, had_frac)) => (rest, v, had_frac),
                            Err(e) => {
                                return Err(e);
                            }
                        };

                        if let Some(r) = parse_relative_restart_i32(unit, rest, frac_u32, had_frac)
                        {
                            return r;
                        }

                        let frac = frac_u32 as Target;

                        if rest.is_empty() {
                            return finalize(unit, frac, rest);
                        }

                        match parse_whole_diagnostic(unit, frac, rest) {
                            Ok((rest, acc)) => finalize(unit, acc, rest),
                            Err(ParseError::EmptyQuantity { .. }) if had_frac => {
                                finalize(unit, frac, rest)
                            }
                            Err(e) => Err(e),
                        }
                    } else {
                        Err(ParseError::EmptyQuantity { unit, at })
                    }
                } else {
                    Err(ParseError::NoUnit { at })
                }
            }

            /// Parse a temperature string, returning [`None`] if there is an error.
            ///
            /// Use [`parse_dim_diagnostic`] if you want to handle specific errors.
            #[inline]
            pub const fn parse_dim(s: &str) -> Option<Target> {
                match parse_dim_diagnostic(s) {
                    Ok(v) => Some(v),
                    _ => None,
                }
            }

            /// Parse a quantity for a known `unit`, returning a [`ParseError`] if parsing fails.
            ///
            /// This parses a single temperature quantity (including origin offsets for relative
            /// scales) for the given [`Unit`].
            #[inline]
            pub const fn parse_as_diagnostic(s: &str, unit: Unit) -> Result<Target, ParseError> {
                let rest = trim_end(s);
                if rest.is_empty() {
                    return Err(ParseError::EmptyQuantity { unit, at: 0 });
                }
                let (rest, frac_u32, had_frac) = match unit.take_decimal_frac(rest) {
                    Ok((rest, v, had_frac)) => (rest, v, had_frac),
                    Err(e) => {
                        return Err(e);
                    }
                };

                if let Some(r) = parse_relative_restart_i32(unit, rest, frac_u32, had_frac) {
                    return r;
                }

                let frac = frac_u32 as Target;

                if rest.is_empty() {
                    return finalize(unit, frac, rest);
                }

                match parse_whole_diagnostic(unit, frac, rest) {
                    Ok((rest, acc)) => finalize(unit, acc, rest),
                    Err(ParseError::EmptyQuantity { .. }) if had_frac => finalize(unit, frac, rest),
                    Err(e) => Err(e),
                }
            }

            /// Parse a quantity for a known `unit`, returning [`None`] if there is an error.
            ///
            /// Use [`parse_as_diagnostic`] if you want to handle specific errors.
            #[inline]
            pub const fn parse_as(s: &str, unit: Unit) -> Option<Target> {
                match parse_as_diagnostic(s, unit) {
                    Ok(v) => Some(v),
                    _ => None,
                }
            }
        }
    };
}

typed_mod!(u32);
typed_mod!(i32);

typed_mod!(u64);
typed_mod!(i64);

typed_mod!(u128);
typed_mod!(i128);

/// Parsing functions for temperature.
pub mod f64 {
    use super::i64::parse_dim as parse_dim_i64;
    use super::i64::parse_dim_diagnostic as parse_dim_diagnostic_i64;
    use super::{strip_unit, trim_end, ParseError};

    /// Maximum contiguous `f64`-safe integer.
    const MAX_SAFE: i64 = (1i64) << f64::MANTISSA_DIGITS;

    /// Parse a temperature string, returning a [`ParseError`] if parsing fails.
    #[inline]
    pub const fn parse_dim_diagnostic(s: &str) -> Result<f64, ParseError> {
        match parse_dim_diagnostic_i64(s) {
            Ok(si) => {
                if si <= MAX_SAFE && si >= -MAX_SAFE {
                    Ok(si as f64)
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

    /// Parse a temperature string, returning [`None`] if there is an error.
    ///
    /// See [`parse_dim_diagnostic`] for information on how to handle errors.
    pub const fn parse_dim(s: &str) -> Option<f64> {
        match parse_dim_i64(s) {
            Some(si) if (si <= MAX_SAFE && si >= -MAX_SAFE) => Some(si as f64),
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

                use joto_constants::temperature::$T::{
                    KELVIN, MILLIKELVIN, RANKINE, SMIDGE, THOUSANDTH_RANKINE, ZERO_CELSIUS,
                    ZERO_FAHRENHEIT,
                };

                /// Const panic wrapper for [`parse_dim`] for better feedback.
                const fn p(s: &str) -> Target {
                    parse_dim(s).unwrap()
                }

                #[test]
                fn invertibility_sanity_check() {
                    const V1: Target = p("100\u{00B0}C") - p("373.15K");
                    assert_eq!(0, V1);
                    const V2: Target = p("32\u{00B0}F") - p("0\u{00B0}C");
                    assert_eq!(0, V2);
                }

                #[test]
                fn basic_parse_dim() {
                    assert_eq!(p("0K"), 0);
                    assert_eq!(p("0\u{00B0}C"), ZERO_CELSIUS);
                    assert_eq!(p("0\u{00B0}F"), ZERO_FAHRENHEIT);
                    assert_eq!(p("459.67\u{00B0}R"), ZERO_FAHRENHEIT);
                }

                #[test]
                fn decimals_parse_dim() {
                    assert_eq!(const { p(".0K") }, 0);
                    assert_eq!(const { p(".0001K") }, 9 * SMIDGE);
                    assert_eq!(parse_dim(".00001K"), None);

                    assert_eq!(const { p(".0mK") }, 0);
                    assert_eq!(const { p(".1mK") }, 9 * SMIDGE);
                    assert_eq!(parse_dim(".01mK"), None);

                    assert_eq!(const { p(".0\u{00B0}R") }, 0);
                    assert_eq!(const { p(".0001\u{00B0}R") }, 5 * SMIDGE);
                    assert_eq!(parse_dim(".00001\u{00B0}R"), None);

                    assert_eq!(const { p(".0\u{00B0}C") }, ZERO_CELSIUS);
                    assert_eq!(const { p(".0001\u{00B0}C") }, ZERO_CELSIUS + 9 * SMIDGE);
                    assert_eq!(parse_dim(".00001\u{00B0}C"), None);

                    assert_eq!(const { p(".0\u{00B0}F") }, ZERO_FAHRENHEIT);
                    assert_eq!(const { p(".0001\u{00B0}F") }, ZERO_FAHRENHEIT + 5 * SMIDGE);
                    assert_eq!(parse_dim(".00001\u{00B0}F"), None);

                    assert_eq!(const { p(".0m\u{00B0}R") }, 0);
                    assert_eq!(const { p(".1m\u{00B0}R") }, 5 * SMIDGE);
                    assert_eq!(parse_dim(".01m\u{00B0}R"), None);
                }

                #[test]
                fn whole_with_separators() {
                    assert_eq!(p("1,000K"), 1_000 * KELVIN);
                    assert_eq!(p("1\u{2008}000mK"), 1_000 * MILLIKELVIN);
                    assert_eq!(p("1\u{2008}000\u{00B0}R"), 1_000 * RANKINE);
                }

                #[test]
                fn sign_parse_dim() {
                    assert_eq!(p("-10\u{00B0}C"), ZERO_CELSIUS - 10 * KELVIN);
                    assert_eq!(p("\u{2212}10\u{00B0}F"), ZERO_FAHRENHEIT - 10 * RANKINE);
                    assert_eq!(p("+10\u{00B0}C"), ZERO_CELSIUS + 10 * KELVIN);
                    assert_eq!(parse_dim("+10K"), None);
                }

                #[test]
                fn parse_diagnostics() {
                    extern crate alloc;
                    use alloc::format;

                    const P1: Target = p("9.0000\u{202F}mK");
                    assert_eq!(P1, 9 * MILLIKELVIN);

                    const P2: Result<Target, ParseError> = parse_dim_diagnostic("9.01mK");
                    assert_eq!(
                        P2,
                        Err(ParseError::TooPrecise {
                            unit: Unit::Millikelvin,
                            at: 4
                        })
                    );

                    const P3: Result<Target, ParseError> = parse_dim_diagnostic("K");
                    assert_eq!(
                        P3,
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Kelvin,
                            at: 0
                        })
                    );

                    const P4: Result<Target, ParseError> = parse_dim_diagnostic("39");
                    assert_eq!(P4, Err(ParseError::NoUnit { at: 2 }));

                    const P5: Result<Target, ParseError> = parse_dim_diagnostic("");
                    assert_eq!(P5, Err(ParseError::Empty));

                    // Empty: entirely whitespace
                    const P6: Result<Target, ParseError> = parse_dim_diagnostic("   ");
                    assert_eq!(P6, Err(ParseError::Empty));

                    // NoUnit: invalid unit suffix
                    const P7: Result<Target, ParseError> = parse_dim_diagnostic("1foo");
                    assert_eq!(P7, Err(ParseError::NoUnit { at: 4 }));

                    // EmptyQuantity: whitespace before unit
                    const P8: Result<Target, ParseError> = parse_dim_diagnostic(" mK ");
                    assert_eq!(
                        P8,
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Millikelvin,
                            at: 1
                        })
                    );

                    // TooPrecise: too many decimal digits for unit
                    const P9: Result<Target, ParseError> = parse_dim_diagnostic("1.00001K");
                    assert_eq!(
                        P9,
                        Err(ParseError::TooPrecise {
                            unit: Unit::Kelvin,
                            at: 7
                        })
                    );

                    let digits = (Target::MAX.ilog10() as usize) + 1;

                    // Overflows when advancing the whole number place value.
                    let p10_str = format!("1{}sd", "0".repeat(digits));
                    let p10: Result<Target, ParseError> = parse_dim_diagnostic(&p10_str);
                    assert_eq!(
                        p10,
                        Err(ParseError::TooBig {
                            unit: Unit::Smidge,
                            at: 1
                        })
                    );

                    // Overflows when adding the place value to the accumulator.
                    let p11_str = format!("1{}sd", "9".repeat(digits));
                    let p11: Result<Target, ParseError> = parse_dim_diagnostic(&p11_str);
                    assert_eq!(
                        p11,
                        Err(ParseError::TooBig {
                            unit: Unit::Smidge,
                            at: 2
                        })
                    );

                    // Overflows when multiplying the place value with the digit.
                    let p12_str = format!("9{}sd", "0".repeat(digits));
                    let p12: Result<Target, ParseError> = parse_dim_diagnostic(&p12_str);
                    assert_eq!(
                        p12,
                        Err(ParseError::TooBig {
                            unit: Unit::Smidge,
                            at: 1
                        })
                    );

                    // Just show that this one works at the limit.
                    let p13: Target = p(format!("{}sd", Target::MAX).as_ref());
                    assert_eq!(p13, Target::MAX);

                    // InvalidSign: signs are not accepted on absolute scales.
                    const P14: Result<Target, ParseError> = parse_dim_diagnostic("-1K");
                    assert_eq!(
                        P14,
                        Err(ParseError::InvalidSign {
                            unit: Unit::Kelvin,
                            at: 0
                        })
                    );

                    const P15: Target = p("1mR");
                    assert_eq!(P15, THOUSANDTH_RANKINE);

                    const P16: Result<Target, ParseError> = parse_dim_diagnostic("-274\u{00B0}C");
                    assert_eq!(
                        P16,
                        Err(ParseError::TooSmall {
                            unit: Unit::Celsius,
                            at: 0
                        })
                    );
                }

                #[test]
                fn parse_as_sanity() {
                    use super::super::$T::parse_as;
                    use super::super::Unit::*;
                    use joto_constants::temperature::$T as t;

                    assert_eq!(parse_as("(unrelated) 1 ", Smidge), Some(t::SMIDGE));
                    assert_eq!(
                        parse_as("(unrelated) 1 ", Millikelvin),
                        Some(t::MILLIKELVIN)
                    );
                    assert_eq!(parse_as("(unrelated) 1 ", Kelvin), Some(t::KELVIN));
                    assert_eq!(
                        parse_as("(unrelated) 1 ", ThousandthRankine),
                        Some(t::THOUSANDTH_RANKINE)
                    );
                    assert_eq!(parse_as("(unrelated) 1 ", Rankine), Some(t::RANKINE));
                    assert_eq!(parse_as("(unrelated) 0 ", Celsius), Some(t::ZERO_CELSIUS));
                    assert_eq!(
                        parse_as("(unrelated) 0 ", Fahrenheit),
                        Some(t::ZERO_FAHRENHEIT)
                    );

                    assert_eq!(parse_as(".0001", Kelvin), Some(9 * t::SMIDGE));
                    assert_eq!(parse_as("   ", Kelvin), None);
                    assert_eq!(parse_as(".01", Millikelvin), None);
                    assert_eq!(parse_as("foo37", Kelvin), Some(37 * t::KELVIN));
                }

                #[test]
                fn parse_as_diagnostic_sanity() {
                    use super::super::$T::parse_as_diagnostic;
                    use super::super::Unit;
                    assert_eq!(
                        parse_as_diagnostic("   ", Unit::Kelvin),
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Kelvin,
                            at: 0
                        })
                    );
                }
            }
        };
    }

    test_submod!(u32);
    test_submod!(i32);
    test_submod!(u64);
    test_submod!(i64);
    test_submod!(u128);
    test_submod!(i128);

    mod f64 {
        use super::super::f64::parse_dim;
        use joto_constants::temperature::f64::{KELVIN, ZERO_CELSIUS};

        #[test]
        fn parse_sanity() {
            assert_eq!(
                parse_dim("-10\u{00B0}C").unwrap(),
                ZERO_CELSIUS - 10. * KELVIN
            );
        }
    }

    #[test]
    fn basic_trim_end() {
        assert_eq!(super::trim_end("foo  \u{202F} "), "foo");
    }
}
