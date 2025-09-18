// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

#![no_std]

use core::ops::Deref;
use core::str;

/// Output from a formatting operation.
#[derive(Clone)]
pub struct FormatOut<const N: usize> {
    /// `true` when the value is exactly represented by the formatted string.
    pub exact: bool,
    /// The start of the valid output string in `buf`.
    start: u8,
    /// The end of the valid output string in `buf`.
    end: u8,
    /// Target buffer ― fixed size buffer for `value`.
    buf: [u8; N],
}

impl<const N: usize> Default for FormatOut<N> {
    fn default() -> Self {
        Self {
            exact: false,
            start: 0,
            end: 0,
            buf: [0u8; N],
        }
    }
}

impl<const N: usize> FormatOut<N> {
    /// Value as bare string slice.
    #[inline(always)]
    pub const fn as_slice(&self) -> &str {
        self.as_str()
    }

    /// Value as bare string slice.
    #[inline(always)]
    pub const fn as_str(&self) -> &str {
        // SAFETY: Region [start..end) is maintained as valid UTF‑8 by construction.
        unsafe {
            let ptr = self.buf.as_ptr().byte_add(self.start as usize);
            let bytes = core::slice::from_raw_parts(ptr, self.len());
            str::from_utf8_unchecked(bytes)
        }
    }

    /// Length of value.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    /// `true` when the value is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.end == self.start
    }
}

impl<const N: usize> Deref for FormatOut<N> {
    type Target = str;

    #[inline(always)]
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsRef<str> for FormatOut<N> {
    #[inline(always)]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

/// Output device mode.
#[derive(Clone, Copy, Default, Debug)]
pub enum OutputDeviceMode {
    /// Use appropriate Unicode for a device or context where Unicode characters like
    /// U+2044 Fraction Slash are likely to be rendered correctly.
    #[default]
    Complex,
    /// Use only plain ASCII in output, for devices which do not do complex shaping, or for which
    /// non-ASCII text is otherwise undesirable.
    Ascii,
}

/// Trait for constant definition of unsigned equivalent of a target primitive type.
trait UnsignedEquivalent {
    type Unsigned;
}
impl UnsignedEquivalent for i128 {
    type Unsigned = u128;
}
impl UnsignedEquivalent for u128 {
    type Unsigned = u128;
}
impl UnsignedEquivalent for i64 {
    type Unsigned = u64;
}
impl UnsignedEquivalent for u64 {
    type Unsigned = u64;
}

pub mod length {
    use super::{FormatOut, OutputDeviceMode};
    pub use joto_parse::Unit;

    /// Formatting hint for feet and inches, used when formatting fractions and mixed units,
    /// which in this module are unique to [`Unit::Foot`] and [`Unit::Inch`].
    #[derive(Clone, Copy, Default, Debug)]
    pub enum FootInchMode {
        /// Format with mixed units for quantities 1 foot or larger, trying standard fractions
        /// before decimal fractions.
        #[default]
        MixedPreferFraction,
        /// Format with mixed units for quantities 1 foot or larger, trying decimal fractions before
        /// standard fractions.
        MixedPreferDecimal,
        /// Format with a single unit, preferring binary fractions 64th and larger when applicable.
        SingleUnitPreferFraction,
        /// Format with a single unit, preferring decimal fractions.
        SingleUnitPreferDecimal,
        /// Format with a single unit, to the nearest binary fraction 1⁄64 or larger when applicable.
        SingleUnitFractionOnly,
        /// Format with a single unit, to the nearest decimal fraction up to the limit.
        SingleUnitDecimalOnly,
    }

    impl FootInchMode {
        /// `true` when this is a mixed unit mode.
        pub const fn is_mixed(&self) -> bool {
            matches!(
                self,
                FootInchMode::MixedPreferDecimal | FootInchMode::MixedPreferFraction
            )
        }

        /// `true` when the mode prefers whole number fractions over decimals.
        pub const fn prefer_fraction(&self) -> bool {
            matches!(
                self,
                FootInchMode::SingleUnitPreferFraction
                    | FootInchMode::MixedPreferFraction
                    | FootInchMode::SingleUnitFractionOnly
            )
        }

        /// `true` when the mode only allows whole number fractions, and not decimals.
        pub const fn fraction_only(&self) -> bool {
            matches!(self, FootInchMode::SingleUnitFractionOnly)
        }
    }

    /// Length formatting options.
    #[derive(Clone, Copy, Default, Debug)]
    pub struct LengthFormat {
        /// Maximum decimal fraction digits.
        ///
        /// By default, the formatter will display as many decimal places as
        /// required for exact representation, if such representation is possible.
        pub max_decimal_fraction_digits: Option<u8>,
        /// Thousands separator, `None` for no separator.
        pub thousands_separator: Option<char>,
        /// feet-inches system formatting hint.
        pub foot_inch_mode: FootInchMode,
        /// Output device mode.
        pub output_device_mode: OutputDeviceMode,
    }

    impl LengthFormat {
        /// Add a thousands separator.
        pub const fn with_separator(mut self, c: char) -> Self {
            self.thousands_separator = Some(c);
            self
        }

        /// Set the thousands separator to an ASCII comma.
        pub const fn with_comma_separator(mut self) -> Self {
            self.thousands_separator = Some(',');
            self
        }

        /// Set the `output_device_mode` to [`OutputDeviceMode::Ascii`].
        pub const fn ascii(mut self) -> Self {
            self.output_device_mode = OutputDeviceMode::Ascii;
            self
        }
    }

    const fn abbr_bytes(unit: Unit, f: LengthFormat) -> &'static [u8] {
        match f.output_device_mode {
            OutputDeviceMode::Complex => unit.abbr().as_bytes(),
            OutputDeviceMode::Ascii => unit.ascii_abbr(),
        }
    }

    /// Maximum length of the fraction and units portion, which is stable across types.
    const REST_BASE_LEN: usize = '.'.len_utf8() + 9 + '\u{202f}'.len_utf8() + '\u{2033}'.len_utf8();

    /// Digit pair lookup table for fast whole number formatting.
    const DIGIT_PAIRS: [u8; 200] = [
        b'0', b'0', b'0', b'1', b'0', b'2', b'0', b'3', b'0', b'4', b'0', b'5', b'0', b'6', b'0',
        b'7', b'0', b'8', b'0', b'9', b'1', b'0', b'1', b'1', b'1', b'2', b'1', b'3', b'1', b'4',
        b'1', b'5', b'1', b'6', b'1', b'7', b'1', b'8', b'1', b'9', b'2', b'0', b'2', b'1', b'2',
        b'2', b'2', b'3', b'2', b'4', b'2', b'5', b'2', b'6', b'2', b'7', b'2', b'8', b'2', b'9',
        b'3', b'0', b'3', b'1', b'3', b'2', b'3', b'3', b'3', b'4', b'3', b'5', b'3', b'6', b'3',
        b'7', b'3', b'8', b'3', b'9', b'4', b'0', b'4', b'1', b'4', b'2', b'4', b'3', b'4', b'4',
        b'4', b'5', b'4', b'6', b'4', b'7', b'4', b'8', b'4', b'9', b'5', b'0', b'5', b'1', b'5',
        b'2', b'5', b'3', b'5', b'4', b'5', b'5', b'5', b'6', b'5', b'7', b'5', b'8', b'5', b'9',
        b'6', b'0', b'6', b'1', b'6', b'2', b'6', b'3', b'6', b'4', b'6', b'5', b'6', b'6', b'6',
        b'7', b'6', b'8', b'6', b'9', b'7', b'0', b'7', b'1', b'7', b'2', b'7', b'3', b'7', b'4',
        b'7', b'5', b'7', b'6', b'7', b'7', b'7', b'8', b'7', b'9', b'8', b'0', b'8', b'1', b'8',
        b'2', b'8', b'3', b'8', b'4', b'8', b'5', b'8', b'6', b'8', b'7', b'8', b'8', b'8', b'9',
        b'9', b'0', b'9', b'1', b'9', b'2', b'9', b'3', b'9', b'4', b'9', b'5', b'9', b'6', b'9',
        b'7', b'9', b'8', b'9', b'9',
    ];

    macro_rules! uabs {
        ( i128, $E:expr ) => {
            ($E).unsigned_abs()
        };
        ( i64, $E:expr ) => {
            ($E).unsigned_abs()
        };
        ( u128, $E:expr ) => {
            ($E)
        };
        ( u64, $E:expr ) => {
            ($E)
        };
    }

    macro_rules! unsigned_mod {
        { $($T:ident),+ } => {
            $(pub mod $T {
                use super::{
                    DIGIT_PAIRS,
                    LengthFormat,
                    REST_BASE_LEN,
                    Unit,
                    abbr_bytes,
                    format_binary_frac,
                    format_decimal_frac,
                };
                use crate::{FormatOut, OutputDeviceMode};

                type UnsignedT = <$T as crate::UnsignedEquivalent>::Unsigned;

                /// Maximum length of the whole number portion of the longest possible output.
                ///
                /// This is enough for ASCII digits for the whole number, where thousands separators
                /// may be 3 bytes (e.g. U+2008) for each group.
                /// Also accommodates U+2032 Prime for foot-inch compounds.
                ///
                /// This is also the end of the whole parts of the quantity.
                #[allow(unused_comparisons, reason = "Some of the types are signed.")]
                const WHOLE_MAX_LEN: usize = if $T::MIN < 0 {
                    '\u{2212}'.len_utf8()
                } else {0} + {$T::MAX.ilog10() as usize + 1}
                    + ($T::MAX.ilog10() / 3) as usize * '\u{2008}'.len_utf8()
                    + '\u{2032}'.len_utf8();

                /// Buffer size to accommodate the longest possible output.
                ///
                /// Accommodates [`WHOLE_MAX_LEN`], an ASCII decimal point, 9 decimal digits
                /// (also covers 2 + 2 ASCII digits and U+2044 for fractions),
                /// bytes for U+2033 Double Prime for inches (longest suffix, same length as
                /// µm `[0xC2, 0xB5, b'm']`), and finally enough bytes for U+202F as a space
                /// between the quantity and the unit.
                const MAX_LEN: usize = WHOLE_MAX_LEN + REST_BASE_LEN;

                pub type LengthFormatOut = FormatOut<MAX_LEN>;

                /// Format a quantity `q` as `unit` into `out`.
                pub const fn format_dim(q: $T, mut unit: Unit, f: LengthFormat) -> LengthFormatOut {
                    let mut out = LengthFormatOut {
                        exact: false,
                        start: WHOLE_MAX_LEN as u8,
                        end: WHOLE_MAX_LEN as u8,
                        buf: [0u8; _],
                    };

                    #[allow(unused_comparisons, reason = "Some of the types are signed.")]
                    let negative = q < 0;
                    let uq = uabs!($T, q);

                    // In mixed modes, always format as the inferior unit when the quantity
                    // is nonzero and less than the primary unit.
                    if uq != 0 && uq < unit as UnsignedT && f.foot_inch_mode.is_mixed() {
                        if let Some(unit_inf) = unit.inferior() {
                            unit = unit_inf
                        }
                    }

                    let mut unit_final = unit;

                    let (quo, mut rem) = (uq / unit as UnsignedT, uq % unit as UnsignedT);

                    if f.foot_inch_mode.is_mixed() {
                        if let Some(unit_inf) = unit.inferior() {
                            if rem != 0 {
                                let (inf_quo, inf_rem) =
                                    (rem / unit_inf as UnsignedT, rem % unit_inf as UnsignedT);
                                if inf_quo != 0 {
                                    format_whole(inf_quo, f, &mut out);
                                    rem = inf_rem;
                                    unit_final = unit_inf;
                                    if quo != 0 {
                                        let b = abbr_bytes(unit, f);
                                        let mut i = b.len();
                                        while i > 0 {
                                            i -= 1;
                                            out.start -= 1;
                                            out.buf[out.start as usize] = b[i];
                                        }
                                    }
                                }
                            }
                        }
                    }

                    if quo == 0 && rem == 0 && out.start == out.end {
                        out.start -= 1;
                        out.buf[out.start as usize] = b'0';
                    } else {
                        format_whole(quo, f, &mut out);
                    }

                    rem = if matches!(unit_final, Unit::Inch) && f.foot_inch_mode.prefer_fraction() {
                        // Only space if we formatted a whole quantity first.
                        let space = out.start != WHOLE_MAX_LEN as u8;
                        let r = format_binary_frac(rem as u64, unit_final, f, space, &mut out)
                            as UnsignedT;
                        if r != 0
                            && f.foot_inch_mode.prefer_fraction()
                            && !f.foot_inch_mode.fraction_only() {
                                // Fallback to decimal if a clean binary fraction was not possible.
                                format_decimal_frac(r as u64, unit_final, f, &mut out) as UnsignedT
                            } else {
                                r
                            }
                    } else {
                        format_decimal_frac(rem as u64, unit_final, f, &mut out) as UnsignedT
                    };

                    out.exact = rem == 0;

                    if !out.exact
                        && out.start == WHOLE_MAX_LEN as u8
                        && out.end == WHOLE_MAX_LEN as u8
                    {
                        // We haven't output any quantities, whole or fraction, but there was
                        // rounding during output, so we should at least add a 0.
                        out.start -= 1;
                        out.buf[out.start as usize] = b'0';
                    }

                    {
                        let b = abbr_bytes(unit_final, f);
                        let mut i = 0;
                        while i < b.len() {
                            out.buf[out.end as usize] = b[i];
                            out.end += 1;
                            i += 1;
                        }
                    }

                    if negative {
                        match f.output_device_mode {
                            OutputDeviceMode::Complex => {
                                let mut minus_buf = [0u8; 4];
                                let minus_bytes = '\u{2212}'.encode_utf8(&mut minus_buf).as_bytes();
                                let mut i = minus_bytes.len();
                                while i > 0 {
                                    i -= 1;
                                    out.start -= 1;
                                    out.buf[out.start as usize] = minus_bytes[i];
                                }
                            }
                            OutputDeviceMode::Ascii => {
                                out.start -= 1;
                                out.buf[out.start as usize] = b'-';
                            }
                        }
                    }

                    out
                }

                /// Format only the whole part of the quantity.
                const fn format_whole(mut quo: UnsignedT, f: LengthFormat, out: &mut LengthFormatOut) {
                    let mut sep_buf = [0u8; 4];
                    let sep = if let Some(c) = f.thousands_separator {
                        c.encode_utf8(&mut sep_buf).as_bytes()
                    } else {
                        b""
                    };

                    let mut pos = 0;
                    macro_rules! write_sep {
                        ($S:expr, $O:expr) => {
                            let mut i = $S.len();
                            while i > 0 {
                                $O.start -= 1;
                                i -= 1;
                                $O.buf[$O.start as usize] = $S[i];
                            }
                        };
                    }

                    while quo > 0 {
                        let chunk = ((quo % 100) as usize) << 1;
                        if pos != 0 && pos % 3 == 0 {
                            write_sep!(sep, out);
                        }
                        out.start -= 1;
                        out.buf[out.start as usize] = DIGIT_PAIRS[chunk + 1];
                        if quo >= 10 {
                            if pos % 3 == 2 {
                                write_sep!(sep, out);
                            }
                            out.start -= 1;
                            out.buf[out.start as usize] = DIGIT_PAIRS[chunk];
                        }
                        quo /= 100;
                        pos += 2;
                    }
                }
            })+
        }
    }

    unsigned_mod! {u128, u64, i128, i64}

    /// Format decimal fraction, returning a remainder if any.
    const fn format_decimal_frac<const N: usize>(
        rem: u64,
        unit: Unit,
        f: LengthFormat,
        out: &mut FormatOut<N>,
    ) -> u64 {
        let lsd = unit.least_significant_digit_value();
        let places = unit.max_decimal_digits();
        let max_places = if let Some(m) = f.max_decimal_fraction_digits {
            if m <= places {
                m
            } else {
                places
            }
        } else {
            places
        };
        let (mut quo, rem) = (rem / lsd as u64, rem % lsd as u64);
        if quo == 0 {
            return rem;
        }
        let num_digits = max_places as usize;
        if (quo.ilog10() + 1) as usize > num_digits {
            let scale = 10u64.pow(num_digits as u32);
            let excess = quo / scale;
            quo %= scale;
            if excess > 0 {
                return rem + excess * lsd as u64;
            }
        }
        let frac_start = out.end as usize;
        out.buf[out.end as usize] = b'.';
        out.end += 1;
        let mut power = 10u64.pow((num_digits - 1) as u32);
        let mut pos = 0;
        while pos < num_digits {
            out.buf[out.end as usize] = b'0' + ((quo / power) % 10) as u8;
            out.end += 1;
            pos += 1;
            if power > 1 {
                power /= 10;
            }
        }
        while out.end > (frac_start + 1) as u8 && out.buf[(out.end - 1) as usize] == b'0' {
            out.end -= 1;
        }
        rem
    }

    /// Format binary fraction down to 64th, returning a remainder if any.
    const fn format_binary_frac<const N: usize>(
        rem: u64,
        unit: Unit,
        f: LengthFormat,
        do_space: bool,
        out: &mut FormatOut<N>,
    ) -> u32 {
        let min_div = (unit as u64) >> 6;
        let (quo, rem) = (rem / min_div, rem % min_div);
        if quo == 0 || rem != 0 || quo > 64 {
            return rem as u32;
        }
        let tz = quo.trailing_zeros() as usize;
        let mag = if tz <= 5 { tz } else { 5 };
        let num = quo >> mag;

        if do_space {
            if let OutputDeviceMode::Complex = f.output_device_mode {
                let mut space_buf = [0u8; 3];
                let space_bytes = '\u{FEFF}'.encode_utf8(&mut space_buf).as_bytes();
                let mut i = 0;
                while i < space_bytes.len() {
                    out.buf[out.end as usize] = space_bytes[i];
                    out.end += 1;
                    i += 1;
                }
            } else {
                out.buf[out.end as usize] = b' ';
                out.end += 1;
            }
        }

        let frac_start = out.end as usize;
        match num {
            1..=9 => {
                out.buf[out.end as usize] = b'0' + num as u8;
                out.end += 1;
            }
            10..=64 => {
                let tens = (num / 10) as u8 + b'0';
                let ones = (num % 10) as u8 + b'0';
                out.buf[out.end as usize] = tens;
                out.end += 1;
                out.buf[out.end as usize] = ones;
                out.end += 1;
            }
            _ => return rem as u32,
        }

        if let OutputDeviceMode::Complex = f.output_device_mode {
            let mut slash_buf = [0u8; 3];
            let slash_bytes = '\u{2044}'.encode_utf8(&mut slash_buf).as_bytes();
            let mut i = 0;
            while i < slash_bytes.len() {
                out.buf[out.end as usize] = slash_bytes[i];
                out.end += 1;
                i += 1;
            }
        } else {
            out.buf[out.end as usize] = b'/';
            out.end += 1;
        }

        match mag {
            5 => {
                out.buf[out.end as usize] = b'2';
                out.end += 1;
            }
            4 => {
                out.buf[out.end as usize] = b'4';
                out.end += 1;
            }
            3 => {
                out.buf[out.end as usize] = b'8';
                out.end += 1;
            }
            2 => {
                out.buf[out.end as usize] = b'1';
                out.end += 1;
                out.buf[out.end as usize] = b'6';
                out.end += 1;
            }
            1 => {
                out.buf[out.end as usize] = b'3';
                out.end += 1;
                out.buf[out.end as usize] = b'2';
                out.end += 1;
            }
            0 => {
                out.buf[out.end as usize] = b'6';
                out.end += 1;
                out.buf[out.end as usize] = b'4';
                out.end += 1;
            }
            _ => return rem as u32,
        }

        while out.end > frac_start as u8 + 1 && out.buf[(out.end - 1) as usize] == b'0' {
            out.end -= 1;
        }

        0
    }
}

#[cfg(test)]
mod tests {
    macro_rules! shared_tests {
        { $($T:ident),+ } => {
            $(mod $T {
                use crate::length::{Unit, LengthFormat, FootInchMode};
                use crate::length::$T::format_dim;
                use joto_constants::length::$T::{
                    FOOT,
                    HUNDRED_THOUSANDTH,
                    INCH,
                    MILLIMETER,
                    SIXTY_FOURTH,
                };
                use joto_parse::$T::parse_dim;

                #[test]
                fn simple() {
                    let o = format_dim(
                        FOOT,
                        Unit::Foot,
                        LengthFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "1′");

                    let o = format_dim(
                        9 * FOOT,
                        Unit::Foot,
                        LengthFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "9′");

                    let o = format_dim(
                        99 * FOOT,
                        Unit::Foot,
                        LengthFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "99′");

                    let o = format_dim(
                        1200 * FOOT,
                        Unit::Foot,
                        LengthFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "1,200′");

                    let o = format_dim(
                        1_200_000 * FOOT,
                        Unit::Foot,
                        LengthFormat::default().with_separator('\u{2008}'),
                    );
                    assert_eq!(o.as_str(), "1\u{2008}200\u{2008}000′");

                    let o = format_dim(
                        1_200_000 * FOOT + INCH,
                        Unit::Foot,
                        LengthFormat::default().with_separator('\u{2008}'),
                    );
                    assert_eq!(o.as_str(), "1\u{2008}200\u{2008}000′1″");

                    let o = format_dim(
                        1_200_000 * FOOT + INCH + 25_000 * HUNDRED_THOUSANDTH,
                        Unit::Foot,
                        LengthFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "1,200,000′1\u{feff}1⁄4″");

                    let o = format_dim(
                        120_000 * FOOT + INCH + 25_000 * HUNDRED_THOUSANDTH,
                        Unit::Foot,
                        LengthFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "120,000′1\u{feff}1⁄4″");

                    let o = format_dim(
                        12_000 * FOOT + INCH + 25_000 * HUNDRED_THOUSANDTH,
                        Unit::Foot,
                        LengthFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "12,000′1\u{feff}1⁄4″");


                    let o = format_dim(
                        1_200_000 * FOOT + INCH + 50_000 * HUNDRED_THOUSANDTH,
                        Unit::Foot,
                        LengthFormat::default().ascii(),
                    );
                    assert_eq!(o.as_str(), "1200000'1 1/2\"");

                    let o = format_dim(
                        1_200_000 * FOOT + INCH + HUNDRED_THOUSANDTH,
                        Unit::Foot,
                        LengthFormat {
                            foot_inch_mode: FootInchMode::MixedPreferDecimal,
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "1200000′1.00001″");

                    let o = format_dim(
                        1_200_000 * FOOT + INCH + INCH / 2,
                        Unit::Meter,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "365760.0381m");

                    let o = format_dim(12345 * MILLIMETER, Unit::Meter, Default::default());
                    assert_eq!(o.as_str(), "12.345m");

                    let o = format_dim(0, Unit::Foot, Default::default());
                    assert_eq!(o.as_str(), "0′");

                    let o = format_dim(FOOT / 2, Unit::Foot, Default::default());
                    assert_eq!(o.as_str(), "6″");

                    let o = format_dim(
                        37 * SIXTY_FOURTH,
                        Unit::Inch,
                        LengthFormat::default().ascii(),
                    );
                    assert_eq!(o.as_ref(), "37/64\"");

                    // Doesn't underrun the buffer or truncate the whole part for the longest
                    // possible output with long separators.
                    assert_eq!(parse_dim(format_dim(
                        $T::MAX,
                        Unit::Iota,
                        LengthFormat::default().with_separator('\u{2008}'),
                    ).as_ref()), Some($T::MAX));
                }
            })+
        }
    }

    #[test]
    fn simple_neg() {
        use crate::length::i128::format_dim;
        use crate::length::{LengthFormat, Unit};
        use joto_constants::length::i128::{FOOT, MILLIMETER, SIXTY_FOURTH};

        let o = format_dim(-12345 * MILLIMETER, Unit::Meter, Default::default());
        assert_eq!(o.as_str(), "\u{2212}12.345m");

        let o = format_dim(
            -12345 * MILLIMETER,
            Unit::Meter,
            LengthFormat::default().ascii(),
        );
        assert_eq!(o.as_ref(), "-12.345m");

        let o = format_dim(-FOOT / 2, Unit::Foot, LengthFormat::default().ascii());
        assert_eq!(o.as_ref(), "-6\"");

        let o = format_dim(
            -(FOOT / 2 + 37 * SIXTY_FOURTH),
            Unit::Foot,
            LengthFormat::default().ascii(),
        );
        assert_eq!(o.as_ref(), "-6 37/64\"");

        let o = format_dim(
            -37 * SIXTY_FOURTH,
            Unit::Inch,
            LengthFormat::default().ascii(),
        );
        assert_eq!(o.as_ref(), "-37/64\"");

        let o = format_dim(
            -37 * SIXTY_FOURTH,
            Unit::Foot,
            LengthFormat::default().ascii(),
        );
        assert_eq!(o.as_ref(), "-37/64\"");

        // Doesn't underrun the buffer or truncate the whole part for the longest
        // possible output with long separators, with U+2212 minus sign.
        assert_eq!(
            format_dim(
                i128::MIN,
                Unit::Iota,
                LengthFormat::default().with_separator('\u{2008}'),
            )
            .as_ref(),
            "−170\u{2008}141\u{2008}183\u{2008}460\u{2008}469\u{2008}231\u{2008}731\u{2008}687\u{2008}303\u{2008}715\u{2008}884\u{2008}105\u{2008}728io"
        );
    }

    shared_tests! {u128, u64, i128, i64}
}
