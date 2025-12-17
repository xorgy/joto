// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Light-weight unit parsing of mass strings into whit.
//!
//! `joto_parse` is intended to offer parsing functions that cover all common dimension parsing
//! needs for typesetting, for architectural and mechanical specification, or for general
//! engineering use.
//! The functions herein can be evaluated in const contexts.
//! They do not panic, they do not allocate, and generally finish parsing in under 50 ns on a
//! laptop.
//!
//! In this workspace, [`WHIT`](joto_constants::mass::u128::WHIT) is defined as 1⁄3200 µg.
//! This allows common divisions of the international pound (ounces, dram, grains) and tenths of a
//! microgram to be represented interchangeably as integers.
//!
//! ## Examples
//! ```rust
//! use joto_constants::mass::u64::{KILOGRAM, OUNCE, POUND};
//! use joto_parse::mass::u64::parse_dim;
//!
//! assert_eq!(parse_dim("2kg").unwrap(), 2 * KILOGRAM);
//! assert_eq!(parse_dim("5lb 3oz").unwrap(), 5 * POUND + 3 * OUNCE);
//! ```

use core::str;

use joto_constants::mass::u64::{
    DRAM, GRAIN, GRAM, KILOGRAM, LONG_HUNDREDWEIGHT, LONG_TON, MEGAGRAM, MICROGRAM, MILLIGRAM,
    OUNCE, PENNYWEIGHT, POUND, SHORT_HUNDREDWEIGHT, SHORT_TON, STONE, TROY_OUNCE, WHIT,
};

/// Unit type for parsing.
///
/// These are distinct from the constants in [`joto_constants`] in the sense that they
/// are meant to represent parsing/generating behavior, and not numeric behavior.
#[derive(Copy, Clone, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
#[repr(u64)]
pub enum Unit {
    /// Whit ― 1⁄3200 µg.
    ///
    /// See [`WHIT`](joto_constants::mass::u128::WHIT).
    Whit = WHIT,
    /// Microgram.
    Microgram = MICROGRAM,
    /// Milligram.
    Milligram = MILLIGRAM,
    /// Gram.
    Gram = GRAM,
    /// Kilogram.
    Kilogram = KILOGRAM,
    /// Megagram ― tonne/metric ton.
    Megagram = MEGAGRAM,
    /// Dram ― exactly 1⁄16 [`Ounce`](Unit::Ounce).
    Dram = DRAM,
    /// Ounce ― exactly 1⁄16 [`Pound`](Unit::Pound).
    Ounce = OUNCE,
    /// Pound ― defined in the [International Yard and Pound agreement].
    ///
    /// [International Yard and Pound agreement]: <https://en.wikipedia.org/wiki/International_yard_and_pound>
    Pound = POUND,
    /// Stone ― exactly 14 [`Pound`](Unit::Pound).
    Stone = STONE,
    /// Long hundredweight ― exactly 8 [`Stone`](Unit::Stone) or 112 [`Pound`](Unit::Pound).
    LongHundredweight = LONG_HUNDREDWEIGHT,
    /// Long ton ― exactly 20 [`LongHundredweight`](Unit::LongHundredweight).
    LongTon = LONG_TON,
    /// Short hundredweight ― exactly 100 [`Pound`](Unit::Pound).
    ShortHundredweight = SHORT_HUNDREDWEIGHT,
    /// Short ton ― exactly 20 [`ShortHundredweight`](Unit::ShortHundredweight).
    ShortTon = SHORT_TON,
    /// Grain ― exactly 1⁄7000 [`Pound`](Unit::Pound).
    Grain = GRAIN,
    /// Pennyweight ― exactly 24 [`Grain`](Unit::Grain).
    Pennyweight = PENNYWEIGHT,
    /// Troy ounce ― exactly 20 [`Pennyweight`](Unit::Pennyweight) or 480 [`Grain`](Unit::Grain).
    TroyOunce = TROY_OUNCE,
    //
    //    ATTENTION:
    //
    //       If you intend to add to this enumeration, make sure you recompute
    //       `unit_phf` and adjust `phf_match_unit_const_map` to match the order.
    //
}

/// Perfect hash function for [`Unit`].
///
/// As with length, matching directly on `Unit as u64` is relatively expensive in code size.
/// This hash enables compact switch tables for unit-derived const functions.
#[inline(always)]
const fn unit_phf(u: Unit) -> u8 {
    (((u as u64).wrapping_mul(3255389357u64) >> 32) & 31) as u8
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
                0 => const { $FN(Whit) },
                25 => const { $FN(Microgram) },
                14 => const { $FN(Milligram) },
                29 => const { $FN(Gram) },
                13 => const { $FN(Kilogram) },
                21 => const { $FN(Megagram) },
                2 => const { $FN(Dram) },
                5 => const { $FN(Ounce) },
                19 => const { $FN(Pound) },
                10 => const { $FN(Stone) },
                22 => const { $FN(LongHundredweight) },
                8 => const { $FN(LongTon) },
                18 => const { $FN(ShortHundredweight) },
                9 => const { $FN(ShortTon) },
                28 => const { $FN(Grain) },
                12 => const { $FN(Pennyweight) },
                16 => const { $FN(TroyOunce) },
                // SAFETY: `Unit` is a closed set, only the values above are reachable.
                _ => unsafe { ::core::hint::unreachable_unchecked() },
            }
        }
    };
}

/// Calculate the value of the least significant decimal fraction digit for a given unit.
const fn unit_lsd_inner(unit: Unit) -> u64 {
    let max_dgt = unit.max_decimal_digits() as u32;
    (unit as u64) / 10u64.pow(max_dgt)
}

phf_match_unit_const_map! {
    /// The base to use when parsing the least significant safe decimal digit.
    #[inline(always)]
    const fn unit_lsd : unit_lsd_inner -> u64
}

/// Maximum number of decimal fraction digits that are exactly represented in whit.
const fn max_decimal_digits_inner(u: Unit) -> u8 {
    use Unit::*;
    match u {
        Whit => 0,
        Microgram => 2,
        Milligram => 5,
        Gram => 8,
        Kilogram => 11,
        Megagram => 14,
        Dram => 0,
        Ounce => 3,
        Pound => 3,
        Stone => 3,
        LongHundredweight => 3,
        LongTon => 4,
        ShortHundredweight => 5,
        ShortTon => 6,
        Grain => 0,
        Pennyweight => 0,
        TroyOunce => 1,
    }
}

phf_match_unit_const_map! {
    /// Maximum number of decimal fraction digits that are exactly represented in whit.
    #[inline(always)]
    const fn max_decimal_digits : max_decimal_digits_inner -> u8
}

impl Unit {
    /// Canonical abbreviation for unit.
    pub const fn abbr(self) -> &'static str {
        use Unit::*;
        match self {
            Whit => "wt",
            Microgram => "µg",
            Milligram => "mg",
            Gram => "g",
            Kilogram => "kg",
            Megagram => "t",
            Dram => "dr",
            Ounce => "oz",
            Pound => "lb",
            Stone => "st",
            LongHundredweight => "cwt.l",
            LongTon => "tn.l",
            ShortHundredweight => "cwt",
            ShortTon => "tn",
            Grain => "gr",
            Pennyweight => "dwt",
            TroyOunce => "ozt",
        }
    }

    /// Canonical ASCII abbreviation for the unit.
    pub const fn ascii_abbr(self) -> &'static [u8] {
        use Unit::*;
        match self {
            Whit => b"wt",
            Microgram => b"ug",
            Milligram => b"mg",
            Gram => b"g",
            Kilogram => b"kg",
            Megagram => b"t",
            Dram => b"dr",
            Ounce => b"oz",
            Pound => b"lb",
            Stone => b"st",
            LongHundredweight => b"cwt_l",
            LongTon => b"tn_l",
            ShortHundredweight => b"cwt",
            ShortTon => b"tn",
            Grain => b"gr",
            Pennyweight => b"dwt",
            TroyOunce => b"ozt",
        }
    }

    /// `true` if the unit is a standard SI unit.
    #[inline]
    pub const fn is_si(self) -> bool {
        use Unit::*;
        matches!(self, Microgram | Milligram | Gram | Kilogram | Megagram)
    }

    /// `Some(Unit)` If `u` has a unit that it is sometimes its superior.
    ///
    /// Useful for parsing compound mass strings like `"5lb 3oz"`.
    #[inline]
    pub const fn superior(self) -> Option<Unit> {
        if matches!(self, Unit::Ounce) {
            Some(Unit::Pound)
        } else {
            None
        }
    }

    /// `Some(Unit)` If `u` has a unit that it is sometimes its inferior.
    #[inline]
    pub const fn inferior(self) -> Option<Unit> {
        if matches!(self, Unit::Pound) {
            Some(Unit::Ounce)
        } else {
            None
        }
    }

    /// Maximum number of decimal fraction digits that are exactly represented in whit.
    #[inline]
    pub const fn max_decimal_digits(self) -> u8 {
        max_decimal_digits(self)
    }

    /// The base to use when parsing the least significant safe decimal digit.
    #[inline]
    pub const fn least_significant_digit_value(self) -> u64 {
        unit_lsd(self)
    }

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

/// Detect a unit at the end of a mass string, returning the rest of the `str` and the [`Unit`].
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
        [r @ .., b'o', b'z', b't'] => (bs(r), Unit::TroyOunce),
        [r @ .., b'd', b'w', b't'] => (bs(r), Unit::Pennyweight),
        [r @ .., b'c', b'w', b't'] => (bs(r), Unit::ShortHundredweight),

        [r @ .., b'c', b'w', b't', b'.' | b'_', b'l'] => {
            (bs(r), Unit::LongHundredweight)
        }
        [r @ .., b't', b'n', b'.' | b'_', b'l'] => {
            (bs(r), Unit::LongTon)
        }

        [r @ .., b'l', b'b'] => (bs(r), Unit::Pound),
        [r @ .., b's', b't'] => (bs(r), Unit::Stone),
        [r @ .., b't', b'n'] => (bs(r), Unit::ShortTon),
        [r @ .., b'd', b'r'] => (bs(r), Unit::Dram),
        [r @ .., b'o', b'z'] => (bs(r), Unit::Ounce),
        [r @ .., b'g', b'r'] => (bs(r), Unit::Grain),

        [r @ .., b'w', b't'] => (bs(r), Unit::Whit),
        [r @ .., b'k', b'g'] => (bs(r), Unit::Kilogram),
        [r @ .., b'm', b'g'] => (bs(r), Unit::Milligram),
        [r @ .., b'm', b'c', b'g'] |
        [r @ .., b'u', b'g'] |
        [r @ .., 0xC2, 0xB5, b'g'] | // U+00B5 Micro Sign
        [r @ .., 0xCE, 0xBC, b'g']   // U+03BC Greek Small Letter Mu
            => (bs(r), Unit::Microgram),

        [r @ .., b'g'] => (bs(r), Unit::Gram),
        [r @ .., b't'] => (bs(r), Unit::Megagram),

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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum ParseError {
    /// Empty or entirely whitespace.
    Empty,
    /// Missing or invalid unit.
    NoUnit {
        /// The point in the string where the issue was encountered.
        at: usize,
    },
    /// Missing quantity portion of the mass.
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

macro_rules! typed_mod {
    ( $T:ident ) => {
        /// Parsing functions for mass.
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

            /// Parse a mass string, returning a [`ParseError`] if parsing fails.
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
                        let (rest, acc) = match unit.take_decimal_frac(rest) {
                            Ok((rest, v)) if !rest.is_empty() => (rest, v as Target),
                            Ok((_, v)) => {
                                return Ok(v as Target);
                            }
                            Err(e) => {
                                return Err(e);
                            }
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

            /// Parse a mass string, returning [`None`] if there is an error.
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
            /// This does not do compound unit parsing, it parses a single quantity for the given
            /// [`Unit`] at the end of `s`.
            #[inline]
            pub const fn parse_as_diagnostic(s: &str, unit: Unit) -> Result<Target, ParseError> {
                let rest = trim_end(s);
                if rest.is_empty() {
                    return Err(ParseError::EmptyQuantity { unit, at: 0 });
                }
                let (rest, acc) = match unit.take_decimal_frac(rest) {
                    Ok((rest, v)) if !rest.is_empty() => (rest, v as Target),
                    Ok((_, v)) => {
                        return Ok(v as Target);
                    }
                    Err(e) => {
                        return Err(e);
                    }
                };
                match parse_whole_diagnostic(unit, acc, rest) {
                    Ok((_, acc)) => Ok(acc),
                    Err(ParseError::EmptyQuantity { .. }) if acc != 0 => Ok(acc),
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

typed_mod!(u64);
typed_mod!(i64);
typed_mod!(u128);
typed_mod!(i128);

/// Parsing functions for mass.
pub mod f64 {
    use super::u64::parse_dim as parse_dim_u64;
    use super::u64::parse_dim_diagnostic as parse_dim_diagnostic_u64;
    use super::{strip_unit, trim_end, ParseError};

    /// Maximum contiguous `f64`-safe integer.
    const MAX_SAFE: u64 = 1 << f64::MANTISSA_DIGITS;

    /// Parse a mass string, returning a [`ParseError`] if parsing fails.
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

    /// Parse a mass string, returning [`None`] if there is an error.
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

                use joto_constants::mass::$T::{
                    GRAM, KILOGRAM, MICROGRAM, MILLIGRAM, OUNCE, POUND, TROY_OUNCE, WHIT,
                };

                /// Const panic wrapper for [`parse_dim`] for better feedback.
                const fn p(s: &str) -> Target {
                    parse_dim(s).unwrap()
                }

                #[test]
                fn invertibility_sanity_check() {
                    const V: Target = p("2kg") + p("3oz") - p("2000g") - p("3.000oz");
                    assert_eq!(0, V)
                }

                #[test]
                fn basic_parse_dim() {
                    assert_eq!(p("37g"), 37 * GRAM);
                    assert_eq!(p("11oz"), 11 * OUNCE);
                    assert_eq!(p("9wt"), 9 * WHIT);
                }

                #[test]
                fn compound_parse_dim() {
                    assert_eq!(p("5lb3oz"), 5 * POUND + 3 * OUNCE);
                    assert_eq!(p("5lb 3oz"), 5 * POUND + 3 * OUNCE);
                    assert_eq!(p("  5lb\u{202F}3oz  "), 5 * POUND + 3 * OUNCE);
                }

                #[test]
                fn si_whole_parse_dim() {
                    assert_eq!(p("1ug"), MICROGRAM);
                    assert_eq!(p("1µg"), MICROGRAM);
                    assert_eq!(p("1μg"), MICROGRAM);
                    assert_eq!(p("1mg"), MILLIGRAM);
                    assert_eq!(p("1g"), GRAM);
                    assert_eq!(p("1kg"), KILOGRAM);
                    assert_eq!(p("1t"), 1_000 * KILOGRAM);

                    assert_eq!(p(" 1 ug "), MICROGRAM);
                    assert_eq!(p(" 1 µg "), MICROGRAM);
                    assert_eq!(p(" 1 μg "), MICROGRAM);
                    assert_eq!(p(" 1 mg "), MILLIGRAM);
                    assert_eq!(p(" 1 g "), GRAM);
                    assert_eq!(p(" 1 kg "), KILOGRAM);
                    assert_eq!(p(" 1 t "), 1_000 * KILOGRAM);
                }

                #[test]
                fn decimal_parse_dim() {
                    assert_eq!(const { p(".0mg") }, 0);
                    assert_eq!(const { p(".00001mg") }, 32 * WHIT);
                    assert_eq!(parse_dim(".000001mg"), None);
                    assert_eq!(const { p(".00000mg") }, 0);

                    assert_eq!(const { p(".0ug") }, 0);
                    assert_eq!(const { p(".01ug") }, MICROGRAM / 100);
                    assert_eq!(parse_dim(".001ug"), None);
                    assert_eq!(const { p(".00ug") }, 0);

                    assert_eq!(const { p(".0oz") }, 0);
                    assert_eq!(const { p(".001oz") }, OUNCE / 1000);
                    assert_eq!(parse_dim(".0001oz"), None);

                    assert_eq!(const { p(".0ozt") }, 0);
                    assert_eq!(const { p(".1ozt") }, TROY_OUNCE / 10);
                    assert_eq!(parse_dim(".01ozt"), None);

                    assert_eq!(parse_dim(".1wt"), None);
                    assert_eq!(parse_dim(".1dr"), None);
                }

                #[test]
                fn whole_with_separators() {
                    assert_eq!(p("1,000g"), 1_000 * GRAM);
                    assert_eq!(p("1\u{2008}000g"), 1_000 * GRAM);
                }

                #[test]
                fn parse_diagnostics() {
                    extern crate alloc;
                    use alloc::format;

                    const P1: Target = p("69g");
                    assert_eq!(P1, GRAM * 69);
                    const P2: Target = p("9.00\u{202F}ug");
                    assert_eq!(P2, 9 * MICROGRAM);
                    const P3: Result<Target, ParseError> = parse_dim_diagnostic("9.001\u{202F}ug");
                    assert_eq!(
                        P3,
                        Err(ParseError::TooPrecise {
                            unit: Unit::Microgram,
                            at: 5
                        })
                    );
                    const P4: Result<Target, ParseError> = parse_dim_diagnostic("ug");
                    assert_eq!(
                        P4,
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Microgram,
                            at: 0
                        })
                    );
                    const P5: Result<Target, ParseError> = parse_dim_diagnostic("39");
                    assert_eq!(P5, Err(ParseError::NoUnit { at: 2 }));
                    const P6: Result<Target, ParseError> = parse_dim_diagnostic("");
                    assert_eq!(P6, Err(ParseError::Empty));

                    // Empty: entirely whitespace
                    const P7: Result<Target, ParseError> = parse_dim_diagnostic("   ");
                    assert_eq!(P7, Err(ParseError::Empty));

                    // NoUnit: invalid unit suffix
                    const P8: Result<Target, ParseError> = parse_dim_diagnostic("1foo");
                    assert_eq!(P8, Err(ParseError::NoUnit { at: 4 }));

                    // EmptyQuantity: whitespace before unit
                    const P9: Result<Target, ParseError> = parse_dim_diagnostic(" oz ");
                    assert_eq!(
                        P9,
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Ounce,
                            at: 1
                        })
                    );

                    // TooPrecise: too many decimal digits for unit
                    const P10: Result<Target, ParseError> = parse_dim_diagnostic("1.0001oz");
                    assert_eq!(
                        P10,
                        Err(ParseError::TooPrecise {
                            unit: Unit::Ounce,
                            at: 6
                        })
                    );

                    // InvalidCompound: superior unit does not match expected for inferior
                    let p11: Result<Target, ParseError> = parse_dim_diagnostic("1kg1oz");
                    assert_eq!(
                        p11,
                        Err(ParseError::InvalidCompound {
                            inferior: Unit::Ounce,
                            found: Unit::Kilogram,
                            at: 3
                        })
                    );

                    let digits = (Target::MAX.ilog10() as usize) + 1;

                    // Overflows when advancing the whole number place value.
                    let p12_str = format!("1{}wt", "0".repeat(digits));
                    let p12: Result<Target, ParseError> = parse_dim_diagnostic(&p12_str);
                    assert_eq!(
                        p12,
                        Err(ParseError::TooBig {
                            unit: Unit::Whit,
                            at: 1
                        })
                    );

                    // Overflows when adding the place value to the accumulator.
                    let p13_str = format!("1{}wt", "9".repeat(digits));
                    let p13: Result<Target, ParseError> = parse_dim_diagnostic(&p13_str);
                    assert_eq!(
                        p13,
                        Err(ParseError::TooBig {
                            unit: Unit::Whit,
                            at: 2
                        })
                    );

                    // Overflows when multiplying the place value with the digit.
                    let p14_str = format!("9{}wt", "0".repeat(digits));
                    let p14: Result<Target, ParseError> = parse_dim_diagnostic(&p14_str);
                    assert_eq!(
                        p14,
                        Err(ParseError::TooBig {
                            unit: Unit::Whit,
                            at: 1
                        })
                    );
                }

                #[test]
                fn parse_as_sanity() {
                    use super::super::$T::parse_as;
                    use super::super::Unit::*;
                    use joto_constants::mass::$T as m;

                    assert_eq!(parse_as("(unrelated) 1 ", Whit), Some(m::WHIT));
                    assert_eq!(parse_as("(unrelated) 1 ", Microgram), Some(m::MICROGRAM));
                    assert_eq!(parse_as("(unrelated) 1 ", Milligram), Some(m::MILLIGRAM));
                    assert_eq!(parse_as("(unrelated) 1 ", Gram), Some(m::GRAM));
                    assert_eq!(parse_as("(unrelated) 1 ", Kilogram), Some(m::KILOGRAM));
                    assert_eq!(parse_as("(unrelated) 1 ", Megagram), Some(m::MEGAGRAM));
                    assert_eq!(parse_as("(unrelated) 1 ", Dram), Some(m::DRAM));
                    assert_eq!(parse_as("(unrelated) 1 ", Ounce), Some(m::OUNCE));
                    assert_eq!(parse_as("(unrelated) 1 ", Pound), Some(m::POUND));
                    assert_eq!(parse_as("(unrelated) 1 ", Stone), Some(m::STONE));
                    assert_eq!(
                        parse_as("(unrelated) 1 ", LongHundredweight),
                        Some(m::LONG_HUNDREDWEIGHT)
                    );
                    assert_eq!(parse_as("(unrelated) 1 ", LongTon), Some(m::LONG_TON));
                    assert_eq!(
                        parse_as("(unrelated) 1 ", ShortHundredweight),
                        Some(m::SHORT_HUNDREDWEIGHT)
                    );
                    assert_eq!(parse_as("(unrelated) 1 ", ShortTon), Some(m::SHORT_TON));
                    assert_eq!(parse_as("(unrelated) 1 ", Grain), Some(m::GRAIN));
                    assert_eq!(
                        parse_as("(unrelated) 1 ", Pennyweight),
                        Some(m::PENNYWEIGHT)
                    );
                    assert_eq!(parse_as("(unrelated) 1 ", TroyOunce), Some(m::TROY_OUNCE));

                    assert_eq!(parse_as(".01", Microgram), Some(m::MICROGRAM / 100));
                    assert_eq!(parse_as("   ", Gram), None);
                    assert_eq!(parse_as(".001", Microgram), None);
                    assert_eq!(parse_as("foo37", Gram), Some(37 * m::GRAM));
                }

                #[test]
                fn parse_as_diagnostic_sanity() {
                    use super::super::$T::parse_as_diagnostic;
                    use super::super::Unit;
                    assert_eq!(
                        parse_as_diagnostic("   ", Unit::Gram),
                        Err(ParseError::EmptyQuantity {
                            unit: Unit::Gram,
                            at: 0
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
        use joto_constants::mass::f64::MICROGRAM;

        #[test]
        fn parse_sanity() {
            assert_eq!(parse_dim("0.01ug").unwrap(), MICROGRAM / 100.);
        }

        #[test]
        fn parse_check_overflow() {
            extern crate alloc;
            use alloc::format;
            assert_eq!(
                parse_dim(format!("{}wt", (1u64 << f64::MANTISSA_DIGITS) + 1).as_ref()),
                None
            );
        }
    }

    #[test]
    fn basic_trim_end() {
        assert_eq!(super::trim_end("foo  \u{202F} "), "foo");
    }
}
