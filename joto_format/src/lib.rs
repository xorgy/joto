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
impl UnsignedEquivalent for i32 {
    type Unsigned = u32;
}
impl UnsignedEquivalent for u32 {
    type Unsigned = u32;
}
impl UnsignedEquivalent for i64 {
    type Unsigned = u64;
}
impl UnsignedEquivalent for u64 {
    type Unsigned = u64;
}

const UTF8_MINUS: [u8; 3] = [0xE2, 0x88, 0x92]; // U+2212 Minus Sign.
const UTF8_FEFF: [u8; 3] = [0xEF, 0xBB, 0xBF]; // U+FEFF Zero Width No-Break Space.
const UTF8_FRACTION_SLASH: [u8; 3] = [0xE2, 0x81, 0x84]; // U+2044 Fraction Slash.
const CHAR_MAX_LEN_UTF8: usize = 4; // `char::MAX_LEN_UTF8` is an unstable feature as of now.

#[inline(always)]
const fn push_byte<const N: usize>(out: &mut FormatOut<N>, b: u8) {
    out.buf[out.end as usize] = b;
    out.end += 1;
}

#[inline(always)]
const fn push_bytes<const N: usize>(out: &mut FormatOut<N>, bytes: &[u8]) {
    let mut i = 0;
    while i < bytes.len() {
        out.buf[out.end as usize] = bytes[i];
        out.end += 1;
        i += 1;
    }
}

#[inline(always)]
const fn prepend_byte<const N: usize>(out: &mut FormatOut<N>, b: u8) {
    out.start -= 1;
    out.buf[out.start as usize] = b;
}

#[inline(always)]
const fn prepend_bytes<const N: usize>(out: &mut FormatOut<N>, bytes: &[u8]) {
    let mut i = bytes.len();
    while i > 0 {
        i -= 1;
        out.start -= 1;
        out.buf[out.start as usize] = bytes[i];
    }
}

#[inline(always)]
const fn prepend_minus<const N: usize>(out: &mut FormatOut<N>, mode: OutputDeviceMode) {
    match mode {
        OutputDeviceMode::Complex => prepend_bytes(out, &UTF8_MINUS),
        OutputDeviceMode::Ascii => prepend_byte(out, b'-'),
    }
}

/// Digit pair lookup table for fast whole number formatting.
const DIGIT_PAIRS: [u8; 200] = [
    b'0', b'0', b'0', b'1', b'0', b'2', b'0', b'3', b'0', b'4', b'0', b'5', b'0', b'6', b'0', b'7',
    b'0', b'8', b'0', b'9', b'1', b'0', b'1', b'1', b'1', b'2', b'1', b'3', b'1', b'4', b'1', b'5',
    b'1', b'6', b'1', b'7', b'1', b'8', b'1', b'9', b'2', b'0', b'2', b'1', b'2', b'2', b'2', b'3',
    b'2', b'4', b'2', b'5', b'2', b'6', b'2', b'7', b'2', b'8', b'2', b'9', b'3', b'0', b'3', b'1',
    b'3', b'2', b'3', b'3', b'3', b'4', b'3', b'5', b'3', b'6', b'3', b'7', b'3', b'8', b'3', b'9',
    b'4', b'0', b'4', b'1', b'4', b'2', b'4', b'3', b'4', b'4', b'4', b'5', b'4', b'6', b'4', b'7',
    b'4', b'8', b'4', b'9', b'5', b'0', b'5', b'1', b'5', b'2', b'5', b'3', b'5', b'4', b'5', b'5',
    b'5', b'6', b'5', b'7', b'5', b'8', b'5', b'9', b'6', b'0', b'6', b'1', b'6', b'2', b'6', b'3',
    b'6', b'4', b'6', b'5', b'6', b'6', b'6', b'7', b'6', b'8', b'6', b'9', b'7', b'0', b'7', b'1',
    b'7', b'2', b'7', b'3', b'7', b'4', b'7', b'5', b'7', b'6', b'7', b'7', b'7', b'8', b'7', b'9',
    b'8', b'0', b'8', b'1', b'8', b'2', b'8', b'3', b'8', b'4', b'8', b'5', b'8', b'6', b'8', b'7',
    b'8', b'8', b'8', b'9', b'9', b'0', b'9', b'1', b'9', b'2', b'9', b'3', b'9', b'4', b'9', b'5',
    b'9', b'6', b'9', b'7', b'9', b'8', b'9', b'9',
];

macro_rules! impl_format_whole {
    ($NAME:ident, $T:ty) => {
        #[inline]
        const fn $NAME<const N: usize>(
            mut quo: $T,
            thousands_separator: Option<char>,
            out: &mut FormatOut<N>,
        ) {
            let mut sep_buf = [0u8; 4];
            let sep = if let Some(c) = thousands_separator {
                c.encode_utf8(&mut sep_buf).as_bytes()
            } else {
                b""
            };

            let mut pos = 0;

            while quo > 0 {
                let chunk = ((quo % 100) as usize) << 1;
                if pos != 0 && pos % 3 == 0 {
                    prepend_bytes(out, sep);
                }
                prepend_byte(out, DIGIT_PAIRS[chunk + 1]);
                if quo >= 10 {
                    if pos % 3 == 2 {
                        prepend_bytes(out, sep);
                    }
                    prepend_byte(out, DIGIT_PAIRS[chunk]);
                }
                quo /= 100;
                pos += 2;
            }
        }
    };
}

impl_format_whole!(format_whole_u32, u32);
impl_format_whole!(format_whole_u64, u64);
impl_format_whole!(format_whole_u128, u128);

macro_rules! format_whole_for_target {
    (u32, $quo:expr, $sep:expr, $out:expr) => {
        $crate::format_whole_u32($quo, $sep, $out)
    };
    (i32, $quo:expr, $sep:expr, $out:expr) => {
        $crate::format_whole_u32($quo, $sep, $out)
    };
    (u64, $quo:expr, $sep:expr, $out:expr) => {
        $crate::format_whole_u64($quo, $sep, $out)
    };
    (i64, $quo:expr, $sep:expr, $out:expr) => {
        $crate::format_whole_u64($quo, $sep, $out)
    };
    (u128, $quo:expr, $sep:expr, $out:expr) => {
        $crate::format_whole_u128($quo, $sep, $out)
    };
    (i128, $quo:expr, $sep:expr, $out:expr) => {
        $crate::format_whole_u128($quo, $sep, $out)
    };
}

#[inline(always)]
const fn cap_decimal_places(places: u8, max_places: Option<u8>) -> u8 {
    if let Some(m) = max_places {
        if m <= places {
            m
        } else {
            places
        }
    } else {
        places
    }
}

#[inline(always)]
const fn scale_lsd_u64(mut lsd: u64, mut places: u8, max_places: u8) -> u64 {
    while places > max_places {
        lsd *= 10;
        places -= 1;
    }
    lsd
}

#[inline(always)]
const fn scale_lsd_u32(mut lsd: u32, mut places: u8, max_places: u8) -> u32 {
    while places > max_places {
        lsd *= 10;
        places -= 1;
    }
    lsd
}

macro_rules! impl_format_decimal_frac {
    ($NAME:ident, $T:ty) => {
        /// Format decimal fraction, returning a remainder if any.
        #[inline(always)]
        const fn $NAME<const N: usize>(
            rem: $T,
            lsd: $T,
            max_places: u8,
            out: &mut FormatOut<N>,
        ) -> $T {
            let (mut quo, rem) = (rem / lsd, rem % lsd);
            if quo == 0 {
                return rem;
            }

            let num_digits = max_places as usize;
            if (quo.ilog10() + 1) as usize > num_digits {
                let scale = (10 as $T).pow(num_digits as u32);
                let excess = quo / scale;
                quo %= scale;
                if excess > 0 {
                    return rem + excess * lsd;
                }
            }

            let frac_start = out.end as usize;
            out.buf[out.end as usize] = b'.';
            out.end += 1;

            let mut power = (10 as $T).pow((num_digits - 1) as u32);
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
    };
}

impl_format_decimal_frac!(format_decimal_frac_u64, u64);
impl_format_decimal_frac!(format_decimal_frac_u32, u32);

/// Allow signed and unsigned quantities to have an unsigned absolute.
macro_rules! uabs {
    ( i128, $E:expr ) => {
        ($E).unsigned_abs()
    };
    ( i32, $E:expr ) => {
        ($E).unsigned_abs()
    };
    ( i64, $E:expr ) => {
        ($E).unsigned_abs()
    };
    ( u32, $E:expr ) => {
        ($E)
    };
    ( u128, $E:expr ) => {
        ($E)
    };
    ( u64, $E:expr ) => {
        ($E)
    };
}

pub mod length {
    use super::{
        cap_decimal_places, format_decimal_frac_u64, push_byte, push_bytes, scale_lsd_u64,
        FormatOut, OutputDeviceMode, UTF8_FEFF, UTF8_FRACTION_SLASH,
    };
    pub use joto_parse::length::Unit;

    /// Fraction type ― decimal or whole number fraction.
    #[derive(Clone, Copy, Default, Debug)]
    pub enum FracType {
        #[default]
        Whole,
        Decimal,
    }

    /// Length formatting options.
    #[derive(Clone, Copy, Debug)]
    pub struct LengthFormat {
        /// Maximum decimal fraction digits.
        ///
        /// By default, the formatter will display as many decimal places as
        /// required for exact representation, if such representation is possible.
        pub max_decimal_fraction_digits: Option<u8>,
        /// Thousands separator, `None` for no separator.
        pub thousands_separator: Option<char>,
        /// Preferred fraction type.
        ///
        /// When the unit supports this fraction type, use it preferentially.
        ///
        /// When [`allow_frac_fallback`] is `true`, the format will try a decimal fraction
        /// as a fallback when supported whole fractions produce a less exact representation.
        pub frac_type: FracType,
        /// Allow a fraction type other than the preferred one, if it is more exact?
        pub allow_frac_fallback: bool,
        /// Allow mixed units in output (e.g. feet and inches)?
        pub mixed: bool,
        /// Output device mode.
        pub output_device_mode: OutputDeviceMode,
    }

    impl LengthFormat {
        /// Make a new [`LengthFormat`] with default options.
        pub const fn new() -> Self {
            Self {
                max_decimal_fraction_digits: None,
                thousands_separator: None,
                frac_type: FracType::Whole,
                allow_frac_fallback: true,
                mixed: true,
                output_device_mode: OutputDeviceMode::Complex,
            }
        }

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

    impl Default for LengthFormat {
        fn default() -> Self {
            Self::new()
        }
    }

    const fn abbr_bytes(unit: Unit, f: LengthFormat) -> &'static [u8] {
        match f.output_device_mode {
            OutputDeviceMode::Complex => unit.abbr().as_bytes(),
            OutputDeviceMode::Ascii => unit.ascii_abbr(),
        }
    }

    /// Maximum length of the fraction and units portion, which is stable across types.
    const REST_BASE_LEN: usize = {
        // Decimal fractions: `.` + 9 digits.
        // Inch fractions: optional U+FEFF + 2 digits + U+2044 + 2 digits.
        const MAX_FRACTION_BYTES: usize = {
            let decimal = '.'.len_utf8() + 9;
            let inch = UTF8_FEFF.len() + 2 + UTF8_FRACTION_SLASH.len() + 2;
            if decimal > inch {
                decimal
            } else {
                inch
            }
        };
        // Longest suffix is 3 bytes (e.g. U+2033 Double Prime or `µm`).
        MAX_FRACTION_BYTES + '\u{2033}'.len_utf8()
    };

    macro_rules! unsigned_mod {
        { $($T:ident),+ } => {
            $(pub mod $T {
                use super::{
                    FracType,
                    LengthFormat,
                    REST_BASE_LEN,
                    Unit,
                    abbr_bytes,
                    format_inch_frac,
                    format_decimal_frac,
                };
                use crate::{prepend_byte, prepend_bytes, prepend_minus, push_bytes, FormatOut, CHAR_MAX_LEN_UTF8};

                type UnsignedT = <$T as crate::UnsignedEquivalent>::Unsigned;

                /// Maximum length of the whole number portion of the longest possible output.
                ///
                /// This is enough for ASCII digits for the whole number, where thousands separators
                /// may be any single Unicode codepoint, so up to 4 bytes.
                ///
                /// Also accommodates U+2032 Prime for foot-inch compounds.
                ///
                /// This is also the end of the whole parts of the quantity.
                #[allow(unused_comparisons, reason = "Some of the types are signed.")]
                const WHOLE_MAX_LEN: usize = if $T::MIN < 0 {
                    '\u{2212}'.len_utf8()
                } else {0} + {$T::MAX.ilog10() as usize + 1}
                    + ($T::MAX.ilog10() / 3) as usize * CHAR_MAX_LEN_UTF8
                    + '\u{2032}'.len_utf8();

                /// Buffer size to accommodate the longest possible output.
                ///
                /// Accommodates [`WHOLE_MAX_LEN`], an ASCII decimal point, 9 decimal digits
                /// (also covers 2 + 2 ASCII digits and U+2044 for fractions),
                /// bytes for U+2033 Double Prime for inches (longest suffix, same length as
                /// µm `[0xC2, 0xB5, b'm']`).
                const MAX_LEN: usize = WHOLE_MAX_LEN + REST_BASE_LEN;

                pub type LengthFormatOut = FormatOut<MAX_LEN>;

                /// Format a quantity `q` as `unit` into `out`.
                pub const fn format_dim(q: $T, mut unit: Unit, f: LengthFormat) -> LengthFormatOut {
                    let mut out = LengthFormatOut {
                        exact: false,
                        start: WHOLE_MAX_LEN as u8,
                        end: WHOLE_MAX_LEN as u8,
                        buf: [0u8; MAX_LEN],
                    };

                    #[allow(unused_comparisons, reason = "Some of the types are signed.")]
                    let negative = q < 0;
                    let uq = uabs!($T, q);

                    // In mixed modes, always format as the inferior unit when the quantity
                    // is nonzero and less than the primary unit.
                    if uq != 0 && uq < unit as UnsignedT && f.mixed {
                        if let Some(unit_inf) = unit.inferior() {
                            unit = unit_inf
                        }
                    }

                    let mut unit_final = unit;

                    let (quo, mut rem) = (uq / unit as UnsignedT, uq % unit as UnsignedT);

                    if f.mixed {
                        if let Some(unit_inf) = unit.inferior() {
                            if rem != 0 {
                                let (inf_quo, inf_rem) =
                                    (rem / unit_inf as UnsignedT, rem % unit_inf as UnsignedT);
                                if inf_quo != 0 {
                                    format_whole_for_target!($T, inf_quo, f.thousands_separator, &mut out);
                                    rem = inf_rem;
                                    unit_final = unit_inf;
                                    if quo != 0 {
                                        let b = abbr_bytes(unit, f);
                                        prepend_bytes(&mut out, b);
                                    }
                                }
                            }
                        }
                    }

                    if quo == 0 && rem == 0 && out.start == out.end {
                        prepend_byte(&mut out, b'0');
                    } else {
                        format_whole_for_target!($T, quo, f.thousands_separator, &mut out);
                    }

                    let (rem, whole_frac) = if matches!(unit_final, Unit::Inch) {
                        // Only space fraction if we formatted a whole quantity first.
                        let space = out.start != WHOLE_MAX_LEN as u8;

                        let rem_primary = match f.frac_type {
                            FracType::Whole => {
                                format_inch_frac(rem as u64, f, space, &mut out) as UnsignedT
                            }
                            FracType::Decimal => {
                                format_decimal_frac(rem as u64, unit_final, f, &mut out) as UnsignedT
                            }
                        };
                        // Try the other fraction type if there was a remainder and fallback is on.
                        if f.allow_frac_fallback && rem_primary != 0 {
                            let end_primary = out.end;
                            let restore: [u8; REST_BASE_LEN] = {
                                let mut restore = [0u8; REST_BASE_LEN];
                                let mut i = restore.len();
                                while i > 0 {
                                    i -= 1;
                                    restore[i] = out.buf[WHOLE_MAX_LEN + i]
                                }
                                restore
                            };
                            // Reset output buffer.
                            out.end = WHOLE_MAX_LEN as u8;
                            let rem_fallback = match f.frac_type {
                                FracType::Whole => {
                                    format_decimal_frac(rem as u64, unit_final, f, &mut out) as UnsignedT
                                }
                                FracType::Decimal => {
                                    format_inch_frac(rem as u64, f, space, &mut out) as UnsignedT
                                }
                            };
                            if rem_fallback < rem_primary {
                                (rem_fallback, matches!(f.frac_type, FracType::Decimal))
                            } else {
                                // Restore the equivalent or superior representation.
                                // When we push MSRV to 1.87 this can just be `copy_from_slice`.
                                let mut i = restore.len();
                                while i > 0 {
                                    i -= 1;
                                    out.buf[WHOLE_MAX_LEN + i] = restore[i];
                                }
                                out.end = end_primary;
                                (rem_primary, matches!(f.frac_type, FracType::Whole))
                            }
                        } else {
                            (rem_primary, matches!(f.frac_type, FracType::Whole))
                        }
                    } else {
                        (format_decimal_frac(rem as u64, unit_final, f, &mut out) as UnsignedT, false)
                    };

                    out.exact = rem == 0;

                    if (!out.exact
                        && out.start == WHOLE_MAX_LEN as u8
                        && out.end == WHOLE_MAX_LEN as u8)
                        ||
                        (out.start == WHOLE_MAX_LEN as u8 && !whole_frac)
                    {
                        // Either we've output nothing at all, or we have written a decimal fraction
                        // and the whole quantity is 0, so at least output one leading 0.
                        prepend_byte(&mut out, b'0');
                    }

                    {
                        let b = abbr_bytes(unit_final, f);
                        push_bytes(&mut out, b);
                    }

                    if negative {
                        prepend_minus(&mut out, f.output_device_mode);
                    }

                    out
                }
            })+
        }
    }

    unsigned_mod! {u128, u64, i128, i64}

    const fn format_decimal_frac<const N: usize>(
        rem: u64,
        unit: Unit,
        f: LengthFormat,
        out: &mut FormatOut<N>,
    ) -> u64 {
        let places = unit.max_decimal_digits();
        let max_places = cap_decimal_places(places, f.max_decimal_fraction_digits);
        let mut lsd = unit.least_significant_digit_value() as u64;
        if max_places < places {
            lsd = scale_lsd_u64(lsd, places, max_places);
            if rem % lsd != 0 {
                return rem;
            }
        }
        format_decimal_frac_u64(rem, lsd, max_places, out)
    }

    /// Format binary fraction down to 64th, returning a remainder if any.
    const fn format_inch_frac<const N: usize>(
        rem: u64,
        f: LengthFormat,
        do_space: bool,
        out: &mut FormatOut<N>,
    ) -> u32 {
        let min_div = (Unit::Inch as u64) >> 6;
        let (quo, rem) = (rem / min_div, rem % min_div);
        if quo == 0 || rem != 0 || quo > 64 {
            return rem as u32;
        }
        let tz = quo.trailing_zeros() as usize;
        let mag = if tz <= 5 { tz } else { 5 };
        let num = quo >> mag;

        if do_space {
            if let OutputDeviceMode::Complex = f.output_device_mode {
                push_bytes(out, &UTF8_FEFF);
            } else {
                push_byte(out, b' ');
            }
        }

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
            push_bytes(out, &UTF8_FRACTION_SLASH);
        } else {
            push_byte(out, b'/');
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

        0
    }
}

pub mod mass {
    use super::{
        cap_decimal_places, format_decimal_frac_u64, scale_lsd_u64, FormatOut, OutputDeviceMode,
    };
    pub use joto_parse::mass::Unit;

    /// Mass formatting options.
    #[derive(Clone, Copy, Debug)]
    pub struct MassFormat {
        /// Maximum decimal fraction digits.
        ///
        /// By default, the formatter will display as many decimal places as
        /// required for exact representation, if such representation is possible.
        pub max_decimal_fraction_digits: Option<u8>,
        /// Thousands separator, `None` for no separator.
        pub thousands_separator: Option<char>,
        /// Output device mode.
        pub output_device_mode: OutputDeviceMode,
    }

    impl MassFormat {
        /// Make a new [`MassFormat`] with default options.
        pub const fn new() -> Self {
            Self {
                max_decimal_fraction_digits: None,
                thousands_separator: None,
                output_device_mode: OutputDeviceMode::Complex,
            }
        }

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

    impl Default for MassFormat {
        fn default() -> Self {
            Self::new()
        }
    }

    const fn abbr_bytes(unit: Unit, f: MassFormat) -> &'static [u8] {
        match f.output_device_mode {
            OutputDeviceMode::Complex => unit.abbr().as_bytes(),
            OutputDeviceMode::Ascii => unit.ascii_abbr(),
        }
    }

    /// Maximum length of the fraction and units portion, which is stable across types.
    const REST_BASE_LEN: usize = '.'.len_utf8() + 14 + "cwt.l".len();

    macro_rules! unsigned_mod {
        { $($T:ident),+ } => {
            $(pub mod $T {
                use super::{
                    MassFormat,
                    REST_BASE_LEN,
                    Unit,
                    abbr_bytes,
                    format_decimal_frac,
                };
                use crate::{prepend_byte, prepend_minus, push_bytes, FormatOut, CHAR_MAX_LEN_UTF8};

                type UnsignedT = <$T as crate::UnsignedEquivalent>::Unsigned;

                /// Maximum length of the whole number portion of the longest possible output.
                ///
                /// This is enough for ASCII digits for the whole number, where thousands separators
                /// may be any single Unicode codepoint, so up to 4 bytes.
                ///
                /// This is also the end of the whole parts of the quantity.
                #[allow(unused_comparisons, reason = "Some of the types are signed.")]
                const WHOLE_MAX_LEN: usize = if $T::MIN < 0 {
                    '\u{2212}'.len_utf8()
                } else {0} + {$T::MAX.ilog10() as usize + 1}
                    + ($T::MAX.ilog10() / 3) as usize * CHAR_MAX_LEN_UTF8;

                /// Buffer size to accommodate the longest possible output.
                ///
                /// Accommodates [`WHOLE_MAX_LEN`], an ASCII decimal point, 14 decimal digits,
                /// and bytes for "cwt.l" (longest suffix).
                const MAX_LEN: usize = WHOLE_MAX_LEN + REST_BASE_LEN;

                pub type MassFormatOut = FormatOut<MAX_LEN>;

                /// Format a quantity `q` as `unit` into `out`.
                pub const fn format_dim(q: $T, unit: Unit, f: MassFormat) -> MassFormatOut {
                    let mut out = MassFormatOut {
                        exact: false,
                        start: WHOLE_MAX_LEN as u8,
                        end: WHOLE_MAX_LEN as u8,
                        buf: [0u8; MAX_LEN],
                    };

                    #[allow(unused_comparisons, reason = "Some of the types are signed.")]
                    let negative = q < 0;
                    let uq = uabs!($T, q);

                    let (quo, rem) = (uq / unit as UnsignedT, uq % unit as UnsignedT);

                    if quo == 0 && rem == 0 && out.start == out.end {
                        prepend_byte(&mut out, b'0');
                    } else {
                        format_whole_for_target!($T, quo, f.thousands_separator, &mut out);
                    }

                    let rem = format_decimal_frac(rem as u64, unit, f, &mut out) as UnsignedT;

                    out.exact = rem == 0;

                    if (!out.exact
                        && out.start == WHOLE_MAX_LEN as u8
                        && out.end == WHOLE_MAX_LEN as u8)
                        || out.start == WHOLE_MAX_LEN as u8
                    {
                        // Either we've output nothing at all, or we have written a decimal fraction
                        // and the whole quantity is 0, so at least output one leading 0.
                        prepend_byte(&mut out, b'0');
                    }

                    {
                        let b = abbr_bytes(unit, f);
                        push_bytes(&mut out, b);
                    }

                    if negative {
                        prepend_minus(&mut out, f.output_device_mode);
                    }

                    out
                }
            })+
        }
    }

    unsigned_mod! {u128, u64, i128, i64}

    const fn format_decimal_frac<const N: usize>(
        rem: u64,
        unit: Unit,
        f: MassFormat,
        out: &mut FormatOut<N>,
    ) -> u64 {
        let places = unit.max_decimal_digits();
        let max_places = cap_decimal_places(places, f.max_decimal_fraction_digits);
        let mut lsd = unit.least_significant_digit_value();
        if max_places < places {
            lsd = scale_lsd_u64(lsd, places, max_places);
            if rem % lsd != 0 {
                return rem;
            }
        }
        format_decimal_frac_u64(rem, lsd, max_places, out)
    }
}

pub mod temperature {
    use super::{
        cap_decimal_places, format_decimal_frac_u32, scale_lsd_u32, FormatOut, OutputDeviceMode,
    };
    pub use joto_parse::temperature::Unit;

    /// Temperature formatting options.
    #[derive(Clone, Copy, Debug)]
    pub struct TemperatureFormat {
        /// Maximum decimal fraction digits.
        ///
        /// By default, the formatter will display as many decimal places as
        /// required for exact representation, if such representation is possible.
        pub max_decimal_fraction_digits: Option<u8>,
        /// Thousands separator, `None` for no separator.
        pub thousands_separator: Option<char>,
        /// Output device mode.
        pub output_device_mode: OutputDeviceMode,
    }

    impl TemperatureFormat {
        /// Make a new [`TemperatureFormat`] with default options.
        pub const fn new() -> Self {
            Self {
                max_decimal_fraction_digits: None,
                thousands_separator: None,
                output_device_mode: OutputDeviceMode::Complex,
            }
        }

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

    impl Default for TemperatureFormat {
        fn default() -> Self {
            Self::new()
        }
    }

    const fn abbr_bytes(unit: Unit, f: TemperatureFormat) -> &'static [u8] {
        match f.output_device_mode {
            OutputDeviceMode::Complex => unit.abbr().as_bytes(),
            OutputDeviceMode::Ascii => unit.ascii_abbr(),
        }
    }

    /// Maximum length of the fraction and units portion, which is stable across types.
    const REST_BASE_LEN: usize = '.'.len_utf8() + 4 + "m°R".len();

    macro_rules! unsigned_mod {
        { $($T:ident),+ } => {
            $(pub mod $T {
                use super::{
                    REST_BASE_LEN,
                    TemperatureFormat,
                    Unit,
                    abbr_bytes,
                    format_decimal_frac,
                };
                use crate::{prepend_byte, prepend_minus, push_bytes, FormatOut, CHAR_MAX_LEN_UTF8};

                type UnsignedT = <$T as crate::UnsignedEquivalent>::Unsigned;

                /// Maximum length of the whole number portion of the longest possible output.
                ///
                /// This is enough for ASCII digits for the whole number, where thousands separators
                /// may be any single Unicode codepoint, so up to 4 bytes.
                ///
                /// Also accommodates U+2212 minus, which is possible for relative units even on
                /// unsigned targets.
                ///
                /// This is also the end of the whole parts of the quantity.
                const WHOLE_MAX_LEN: usize = '\u{2212}'.len_utf8()
                    + {$T::MAX.ilog10() as usize + 1}
                    + ($T::MAX.ilog10() / 3) as usize * CHAR_MAX_LEN_UTF8;

                /// Buffer size to accommodate the longest possible output.
                ///
                /// Accommodates [`WHOLE_MAX_LEN`], an ASCII decimal point, 4 decimal digits,
                /// and bytes for "m°R" (longest suffix).
                const MAX_LEN: usize = WHOLE_MAX_LEN + REST_BASE_LEN;

                pub type TemperatureFormatOut = FormatOut<MAX_LEN>;

                /// Format a quantity `q` as `unit` into `out`.
                pub const fn format_dim(q: $T, unit: Unit, f: TemperatureFormat) -> TemperatureFormatOut {
                    let mut out = TemperatureFormatOut {
                        exact: false,
                        start: WHOLE_MAX_LEN as u8,
                        end: WHOLE_MAX_LEN as u8,
                        buf: [0u8; MAX_LEN],
                    };

                    let origin_u = unit.origin_offset() as UnsignedT;

                    #[allow(unused_comparisons, reason = "Some of the types are unsigned.")]
                    let q_negative = q < 0 as $T;

                    let (negative, uq) = if origin_u != 0 {
                        if q_negative {
                            // delta < 0: origin - q == origin + abs(q)
                            let uq = uabs!($T, q);
                            // SAFETY: sum cannot overflow for supported integer widths with u32 origin.
                            (true, unsafe { origin_u.unchecked_add(uq) })
                        } else {
                            let uq = q as UnsignedT;
                            if uq < origin_u {
                                (true, origin_u - uq)
                            } else {
                                (false, uq - origin_u)
                            }
                        }
                    } else if q_negative {
                        (true, uabs!($T, q))
                    } else {
                        (false, q as UnsignedT)
                    };

                    let scale = unit.scale() as UnsignedT;
                    let (quo, rem) = (uq / scale, (uq % scale) as u32);

                    if quo == 0 && rem == 0 && out.start == out.end {
                        prepend_byte(&mut out, b'0');
                    } else {
                        format_whole_for_target!($T, quo, f.thousands_separator, &mut out);
                    }

                    let rem = format_decimal_frac(rem, unit, f, &mut out);

                    out.exact = rem == 0;

                    if (!out.exact
                        && out.start == WHOLE_MAX_LEN as u8
                        && out.end == WHOLE_MAX_LEN as u8)
                        || out.start == WHOLE_MAX_LEN as u8
                    {
                        // Either we've output nothing at all, or we have written a decimal fraction
                        // and the whole quantity is 0, so at least output one leading 0.
                        prepend_byte(&mut out, b'0');
                    }

                    {
                        let b = abbr_bytes(unit, f);
                        push_bytes(&mut out, b);
                    }

                    if negative {
                        prepend_minus(&mut out, f.output_device_mode);
                    }

                    out
                }
            })+
        }
    }

    unsigned_mod! {u32, i32, u64, i64, u128, i128}

    const fn format_decimal_frac<const N: usize>(
        rem: u32,
        unit: Unit,
        f: TemperatureFormat,
        out: &mut FormatOut<N>,
    ) -> u32 {
        let places = unit.max_decimal_digits();
        let max_places = cap_decimal_places(places, f.max_decimal_fraction_digits);
        let mut lsd = unit.least_significant_digit_value();
        if max_places < places {
            lsd = scale_lsd_u32(lsd, places, max_places);
            if rem % lsd != 0 {
                return rem;
            }
        }
        format_decimal_frac_u32(rem, lsd, max_places, out)
    }
}

#[cfg(test)]
mod tests {
    macro_rules! shared_tests {
        { $($T:ident),+ } => {
            $(mod $T {
                use crate::length::{Unit, LengthFormat, FracType};
                use crate::length::$T::format_dim;
                use joto_constants::length::$T::{
                    FOOT,
                    HUNDRED_THOUSANDTH,
                    INCH,
                    IOTA,
                    MILLIMETER,
                    NANOMETER,
                    SIXTY_FOURTH,
                };
                use joto_parse::length::$T::parse_dim;

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
                            frac_type: FracType::Decimal,
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "1200000′1.00001″");

                    // Inch fallback must not truncate the chosen representation.
                    let o = format_dim(
                        INCH + HUNDRED_THOUSANDTH + IOTA,
                        Unit::Inch,
                        LengthFormat {
                            frac_type: FracType::Decimal,
                            allow_frac_fallback: true,
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "1.00001″");
                    assert!(!o.exact);

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

                    let o = format_dim(
                        HUNDRED_THOUSANDTH,
                        Unit::Inch,
                        LengthFormat::default(),
                    );
                    assert_eq!(o.as_ref(), "0.00001″");

                    let o = format_dim(
                        NANOMETER,
                        Unit::Meter,
                        LengthFormat::default(),
                    );
                    assert_eq!(o.as_ref(), "0.000000001m");
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

#[cfg(test)]
mod temperature_tests {
    macro_rules! shared_tests {
        { $($T:ident),+ } => {
            $(mod $T {
                use crate::temperature::{TemperatureFormat, Unit};
                use crate::temperature::$T::format_dim;
                use joto_constants::temperature::$T::{
                    KELVIN, MILLIKELVIN, RANKINE, SMIDGE, THOUSANDTH_RANKINE, ZERO_CELSIUS,
                    ZERO_FAHRENHEIT,
                };

                #[test]
                fn simple() {
                    let o = format_dim(373 * KELVIN + 150 * MILLIKELVIN, Unit::Kelvin, Default::default());
                    assert_eq!(o.as_str(), "373.15K");
                    assert!(o.exact);

                    let o = format_dim(ZERO_CELSIUS + 100 * KELVIN, Unit::Celsius, Default::default());
                    assert_eq!(o.as_str(), "100°C");
                    assert!(o.exact);

                    let o = format_dim(
                        ZERO_FAHRENHEIT + 32 * RANKINE,
                        Unit::Fahrenheit,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "32°F");
                    assert!(o.exact);

                    let o = format_dim(0, Unit::Celsius, Default::default());
                    assert_eq!(o.as_str(), "−273.15°C");
                    assert!(o.exact);

                    let o = format_dim(0, Unit::Fahrenheit, Default::default());
                    assert_eq!(o.as_str(), "−459.67°F");
                    assert!(o.exact);

                    let o = format_dim(THOUSANDTH_RANKINE, Unit::ThousandthRankine, Default::default());
                    assert_eq!(o.as_str(), "1m°R");
                    assert!(o.exact);

                    let o = format_dim(SMIDGE, Unit::Smidge, Default::default());
                    assert_eq!(o.as_str(), "1sd");
                    assert!(o.exact);

                    let o = format_dim(
                        ZERO_CELSIUS + 12_345 * KELVIN,
                        Unit::Celsius,
                        TemperatureFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "12,345°C");
                    assert!(o.exact);

                    let o = format_dim(
                        ZERO_CELSIUS,
                        Unit::Celsius,
                        TemperatureFormat::default().ascii(),
                    );
                    assert_eq!(o.as_str(), "0C");
                    assert!(o.exact);

                    let o = format_dim(
                        THOUSANDTH_RANKINE,
                        Unit::ThousandthRankine,
                        TemperatureFormat::default().ascii(),
                    );
                    assert_eq!(o.as_str(), "1mR");
                    assert!(o.exact);

                    // Smallest exact Kelvin decimal.
                    let o = format_dim(KELVIN / 10_000, Unit::Kelvin, Default::default());
                    assert_eq!(o.as_str(), "0.0001K");
                    assert!(o.exact);

                    // Leading zero decimals must not be rescaled when limiting places.
                    let o = format_dim(
                        KELVIN / 10_000,
                        Unit::Kelvin,
                        TemperatureFormat {
                            max_decimal_fraction_digits: Some(1),
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "0K");
                    assert!(!o.exact);

                    // Trailing zero decimals remain representable at reduced precision.
                    let o = format_dim(
                        KELVIN / 10,
                        Unit::Kelvin,
                        TemperatureFormat {
                            max_decimal_fraction_digits: Some(1),
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "0.1K");
                    assert!(o.exact);

                    // Inexact when limiting to fewer fixed decimal places.
                    let o = format_dim(
                        123 * KELVIN + 4567 * (KELVIN / 10_000),
                        Unit::Kelvin,
                        TemperatureFormat {
                            max_decimal_fraction_digits: Some(3),
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "123K");
                    assert!(!o.exact);
                }
            })+
        }
    }

    shared_tests! {u32, i32, u64, i64, u128, i128}
}

#[cfg(test)]
mod mass_tests {
    macro_rules! shared_tests {
        { $($T:ident),+ } => {
            $(mod $T {
                use crate::mass::{Unit, MassFormat};
                use crate::mass::$T::format_dim;
                use joto_constants::mass::$T::{
                    GRAIN, GRAM, KILOGRAM, MEGAGRAM, MICROGRAM,
                    MILLIGRAM, OUNCE, POUND, SHORT_TON, TROY_OUNCE,
                };

                #[test]
                fn simple() {
                    let o = format_dim(
                        POUND,
                        Unit::Pound,
                        MassFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "1lb");
                    assert!(o.exact);

                    let o = format_dim(
                        9 * POUND,
                        Unit::Pound,
                        MassFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "9lb");
                    assert!(o.exact);

                    let o = format_dim(
                        99 * POUND,
                        Unit::Pound,
                        MassFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "99lb");
                    assert!(o.exact);

                    let o = format_dim(
                        1200 * POUND,
                        Unit::Pound,
                        MassFormat::default().with_comma_separator(),
                    );
                    assert_eq!(o.as_str(), "1,200lb");
                    assert!(o.exact);

                    let o = format_dim(
                        1_200_000 * POUND,
                        Unit::Pound,
                        MassFormat::default().with_separator('\u{2008}'),
                    );
                    assert_eq!(o.as_str(), "1\u{2008}200\u{2008}000lb");
                    assert!(o.exact);

                    let o = format_dim(
                        1_200_000 * POUND + OUNCE,
                        Unit::Pound,
                        MassFormat::default().with_separator('\u{2008}'),
                    );
                    assert_eq!(o.as_str(), "1\u{2008}200\u{2008}000.062lb");
                    assert!(!o.exact);

                    let o = format_dim(
                        1_200_000 * POUND + OUNCE / 2,
                        Unit::Kilogram,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "544310.85817476156kg");
                    assert!(!o.exact);

                    let o = format_dim(12345 * MILLIGRAM, Unit::Gram, Default::default());
                    assert_eq!(o.as_str(), "12.345g");
                    assert!(o.exact);

                    let o = format_dim(0, Unit::Pound, Default::default());
                    assert_eq!(o.as_str(), "0lb");
                    assert!(o.exact);

                    let o = format_dim(MEGAGRAM / 2, Unit::Megagram, Default::default());
                    assert_eq!(o.as_str(), "0.5t");
                    assert!(o.exact);

                    let o = format_dim(
                        MEGAGRAM / 1000,
                        Unit::Megagram,
                        Default::default(),
                    );
                    assert_eq!(o.as_ref(), "0.001t");
                    assert!(o.exact);

                    let o = format_dim(
                        MICROGRAM,
                        Unit::Kilogram,
                        Default::default(),
                    );
                    assert_eq!(o.as_ref(), "0.000000001kg");
                    assert!(o.exact);

                    let o = format_dim(
                        MICROGRAM / 100,
                        Unit::Microgram,
                        Default::default(),
                    );
                    assert_eq!(o.as_ref(), "0.01µg");
                    assert!(o.exact);

                    // Limiting fractional digits must not rescale leading-zero decimals.
                    let o = format_dim(
                        MICROGRAM / 100,
                        Unit::Microgram,
                        MassFormat {
                            max_decimal_fraction_digits: Some(1),
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "0µg");
                    assert!(!o.exact);

                    // Trailing-zero decimals remain representable at reduced precision.
                    let o = format_dim(
                        MICROGRAM / 10,
                        Unit::Microgram,
                        MassFormat {
                            max_decimal_fraction_digits: Some(1),
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "0.1µg");
                    assert!(o.exact);

                    // Test max decimal digits for microgram (2)
                    let o = format_dim(
                        MICROGRAM + MICROGRAM / 100,
                        Unit::Microgram,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1.01µg");
                    assert!(o.exact);

                    let o = format_dim(
                        MICROGRAM + MICROGRAM / 1000,
                        Unit::Microgram,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1µg");
                    assert!(!o.exact);

                    // Test limiting decimal places
                    let o = format_dim(
                        GRAM + GRAM / 1000,
                        Unit::Gram,
                        MassFormat {
                            max_decimal_fraction_digits: Some(2),
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "1g");
                    assert!(!o.exact);

                    // Test for troy ounce (max 1 decimal)
                    let o = format_dim(
                        TROY_OUNCE + TROY_OUNCE / 10,
                        Unit::TroyOunce,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1.1ozt");
                    assert!(o.exact);

                    let o = format_dim(
                        TROY_OUNCE + TROY_OUNCE / 100,
                        Unit::TroyOunce,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1ozt");
                    assert!(!o.exact);

                    // Test short ton (max 6 decimals)
                    let o = format_dim(
                        SHORT_TON + SHORT_TON / 1000000,
                        Unit::ShortTon,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1.000001tn");
                    assert!(o.exact);

                    let o = format_dim(
                        SHORT_TON + SHORT_TON / 10000000,
                        Unit::ShortTon,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1tn");
                    assert!(!o.exact);

                    // Test exact whole number in fractional unit
                    let o = format_dim(
                        GRAIN * 7000,
                        Unit::Pound,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1lb");
                    assert!(o.exact);

                    // Test inexact with max decimals limited
                    let o = format_dim(
                        KILOGRAM + KILOGRAM / 1000000000000,
                        Unit::Kilogram,
                        MassFormat {
                            max_decimal_fraction_digits: Some(10),
                            ..Default::default()
                        },
                    );
                    assert_eq!(o.as_str(), "1kg");
                    assert!(!o.exact);

                    // Test zero fractional part not displaying decimal
                    let o = format_dim(
                        MILLIGRAM * 1000,
                        Unit::Gram,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1g");
                    assert!(o.exact);

                    // Test trimming trailing zeros
                    let o = format_dim(
                        GRAM + GRAM / 10,
                        Unit::Gram,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1.1g");
                    assert!(o.exact);

                    let o = format_dim(
                        GRAM + GRAM / 100,
                        Unit::Gram,
                        Default::default(),
                    );
                    assert_eq!(o.as_str(), "1.01g");
                    assert!(o.exact);
                }
            })+
        }
    }

    #[test]
    fn simple_neg() {
        use crate::mass::i128::format_dim;
        use crate::mass::{MassFormat, Unit};
        use joto_constants::mass::i128::{
            DRAM, GRAIN, GRAM, KILOGRAM, MEGAGRAM, MICROGRAM, MILLIGRAM, OUNCE, TROY_OUNCE,
        };

        let o = format_dim(-12345 * GRAM, Unit::Kilogram, Default::default());
        assert_eq!(o.as_str(), "\u{2212}12.345kg");
        assert!(o.exact);

        let o = format_dim(-12345 * GRAM, Unit::Kilogram, MassFormat::default().ascii());
        assert_eq!(o.as_ref(), "-12.345kg");
        assert!(o.exact);

        let o = format_dim(-MEGAGRAM / 2, Unit::Megagram, MassFormat::default().ascii());
        assert_eq!(o.as_ref(), "-0.5t");
        assert!(o.exact);

        let o = format_dim(
            -MICROGRAM / 100,
            Unit::Microgram,
            MassFormat::default().ascii(),
        );
        assert_eq!(o.as_ref(), "-0.01ug");
        assert!(o.exact);

        // Doesn't underrun the buffer or truncate the whole part for the longest
        // possible output with long separators, with U+2212 minus sign.
        assert_eq!(
            format_dim(
                i128::MIN,
                Unit::Whit,
                MassFormat::default().with_separator('\u{2008}'),
            )
            .as_ref(),
            "−170\u{2008}141\u{2008}183\u{2008}460\u{2008}469\u{2008}231\u{2008}731\u{2008}687\u{2008}303\u{2008}715\u{2008}884\u{2008}105\u{2008}728wt"
        );

        let o = format_dim(-OUNCE / 1000, Unit::Ounce, MassFormat::default().ascii());
        assert_eq!(o.as_ref(), "-0.001oz");
        assert!(o.exact);

        let o = format_dim(-DRAM, Unit::Dram, MassFormat::default());
        assert_eq!(o.as_str(), "−1dr");
        assert!(o.exact);

        let o = format_dim(-GRAIN / 2, Unit::Grain, MassFormat::default().ascii());
        assert_eq!(o.as_ref(), "-0gr");
        assert!(!o.exact);

        let o = format_dim(-TROY_OUNCE / 10, Unit::TroyOunce, Default::default());
        assert_eq!(o.as_str(), "−0.1ozt");
        assert!(o.exact);

        let o = format_dim(-MILLIGRAM / 10000, Unit::Milligram, Default::default());
        assert_eq!(o.as_str(), "−0.0001mg");
        assert!(o.exact);

        let o = format_dim(
            -KILOGRAM + KILOGRAM / 100000000000,
            Unit::Kilogram,
            MassFormat {
                max_decimal_fraction_digits: Some(11),
                ..Default::default()
            },
        );
        assert_eq!(o.as_str(), "−0.99999999999kg");
        assert!(o.exact);
    }

    shared_tests! {u128, u64, i128, i64}
}
