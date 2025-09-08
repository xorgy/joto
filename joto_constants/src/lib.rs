// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Constants for interoperation of units.
//!
//! # Operating principle
//!
//! Here we set out to interoperate US Customary and SI units of length/displacement, mass, and
//! temperature, while preserving invertibility, avoiding uncontrolled precision loss, and replacing
//! structured unit types ― which are tricky to store or compute efficiently ― with plain integers.
//!
//! This is accomplished by defining common base units for length, mass, and temperature, which can
//! be used to express [US customary units] and [SI units] in the same scale for each domain.
//!
//! ## [`length`]
//!
//! [`u128`](length::u128) | [`i128`](length::i128) |
//! [`u64`](length::u64) | [`i64`](length::i64) |
//! [`f64`](length::f64)
//!
//! For length, there is the *iota*, defined as 1⁄9 nm.
//!
//! This allows common fractions of an inch (ten-thousandths, desktop publishing points, and
//! sixty-fourths) and multiples of the nanometer to be represented as natural numbers.
//!
//!
//! ## [`mass`]
//!
//! [`u128`](mass::u128) | [`i128`](mass::i128) |
//! [`u64`](mass::u64) | [`i64`](mass::i64) |
//! [`f64`](mass::f64)
//!
//! For mass, there is the *whit*, defined as 1⁄3200 µg.
//!
//! The whit is chosen to express practically measurable weights (down to the 0.1 µg range) as well
//! as all common fractional denominations of the international pound (ounces, dram, thousandths of
//! an ounce, grains) and units related to the pound by grains (such as the troy ounce).
//!
//!
//! ## [`temperature`]
//!
//! [`u128`](temperature::u128) | [`i128`](temperature::i128) |
//! [`u64`](temperature::u64) | [`i64`](temperature::i64) |
//! [`u32`](temperature::u32) | [`i32`](temperature::i32) |
//! [`f64`](temperature::f64)
//!
//! For temperature, there is the *smidge*, defined as 1⁄90 mK.
//!
//! The smidge represents temperatures down to the 100 µK/0.0001 °R range, which is sufficient for
//! almost all practical thermometry. This also allows you to exactly represent temperatures used in
//! industrial metrology standards such as [ITS-90] for fixed points and common derived constants,
//! and allows exact interchange between common absolute (Kelvin/[Rankine]) and relative
//! (Celsius/Fahrenheit) temperature scales.
//!
//! The [`temperature`] module deliberately avoids defining incremental units of temperature by
//! their relative scale names, to remind users to account for the difference in origin/zero point
//! between Fahrenheit and Celsius.
//!
//! [SI units]: <https://en.wikipedia.org/wiki/International_System_of_Units>
//! [US customary units]: <https://en.wikipedia.org/wiki/United_States_customary_units>
//! [ITS-90]: <https://en.wikipedia.org/wiki/International_Temperature_Scale_of_1990>
//! [Rankine]: <https://en.wikipedia.org/wiki/Rankine_scale>

#![no_std]

/// Per-target-type modules for units of length denominated in ‘iota’ ― 1⁄9 nm increments.
///
/// This allows common fractions of an inch (ten-thousandths, desktop publishing points, and
/// sixty-fourths) and multiples of the nanometer to be represented as natural numbers.
///
/// # Type selection
///
/// [i64](length::i64) can express displacements ± 1 024 819 115 m or ± 3 362 267 438 ft, so is
/// more than sufficient for general use in linear displacements.
/// When using iota for *area* or for *volume*, these grow by square and cube, so it is advisable
/// to consider whether your working quantities will need a larger type.
/// [i128](length::i128) can express volumetric quantities ± 233 389 826 m³ or ± 8 242 083 936 cuft.
pub mod length {
    macro_rules! typed_mod {
        ( $T:ident ) => {
            /// Constants for common units of length.
            pub mod $T {
                /// One ninth of a nanometer.
                ///
                /// This allows common fractions of an [`INCH`] ([`TEN_THOUSANDTH`], [`POINT`],
                /// [`SIXTY_FOURTH`]) and [`NANOMETER`] to be represented as integers.
                ///
                /// Using this base unit, combinations of lengths in either [US customary units] or
                /// [SI units] can be added, subtracted, multiplied, and often divided without loss.
                ///
                /// [US customary units]: <https://en.wikipedia.org/wiki/United_States_customary_units>
                /// [SI units]: <https://en.wikipedia.org/wiki/International_System_of_Units>
                pub const IOTA: $T = 1 as $T;

                /// Nanometer.
                pub const NANOMETER: $T = 9 as $T * IOTA;
                /// Micrometer.
                #[doc(alias = "MICRON")]
                pub const MICROMETER: $T = 1_000 as $T * NANOMETER;
                /// 1⁄4 [`MILLIMETER`] a.k.a. ‘Q’.
                ///
                /// This unit is used in typography, particularly in Japan.
                #[doc(alias = "Q")]
                pub const QUARTER_MILLIMETER: $T = 250 as $T * MICROMETER;
                /// Millimeter.
                pub const MILLIMETER: $T = 1_000 as $T * MICROMETER;
                /// Centimeter.
                pub const CENTIMETER: $T = 10 as $T * MILLIMETER;
                /// Decimeter.
                pub const DECIMETER: $T = 10 as $T * CENTIMETER;
                /// Meter.
                pub const METER: $T = 1_000 as $T * MILLIMETER;

                /// 1⁄64 [`INCH`].
                pub const SIXTY_FOURTH: $T = 3_571_875 as $T * IOTA;
                /// 1⁄32 [`INCH`].
                pub const THIRTY_SECOND: $T = 2 as $T * SIXTY_FOURTH;
                /// 1⁄16 [`INCH`].
                pub const SIXTEENTH: $T = 2 as $T * THIRTY_SECOND;
                /// 1⁄8 [`INCH`].
                pub const EIGHTH: $T = 2 as $T * SIXTEENTH;
                /// 1⁄4 [`INCH`].
                pub const QUARTER: $T = 2 as $T * EIGHTH;
                /// 1⁄2 [`INCH`].
                pub const HALF: $T = 2 as $T * QUARTER;
                /// 1⁄100000 [`INCH`].
                pub const HUNDRED_THOUSANDTH: $T = 2_286 as $T * IOTA;
                /// 1⁄10000 [`INCH`].
                pub const TEN_THOUSANDTH: $T = 10 as $T * HUNDRED_THOUSANDTH;
                /// 1⁄1000 [`INCH`].
                #[doc(alias = "MIL")]
                #[doc(alias = "THOUSANDTH_INCH")]
                pub const THOU: $T = 10 as $T * TEN_THOUSANDTH;
                /// One [desktop publishing point](<https://en.wikipedia.org/wiki/Point_(typography)#Desktop_publishing_point>).
                ///
                /// Exactly 1⁄72 of an [`INCH`] or 1⁄12 of a [`PICA`].
                pub const POINT: $T = 3_175_000 as $T * IOTA;
                /// Pica ― exactly 1⁄6 [`INCH`] or 12 [`POINT`].
                pub const PICA: $T = 12 as $T * POINT;
                /// Inch ― exactly 1⁄12 [`FOOT`].
                pub const INCH: $T = 6 as $T * PICA;
                /// Foot ― exactly 1⁄3 [`YARD`].
                pub const FOOT: $T = 12 as $T * INCH;
                /// Yard ― as defined in the [International Yard and Pound agreement].
                ///
                /// [International Yard and Pound agreement]: <https://en.wikipedia.org/wiki/International_yard_and_pound>
                pub const YARD: $T = 3 as $T * FOOT;
            }
        };
    }

    typed_mod!(i64);
    typed_mod!(u64);

    typed_mod!(u128);
    typed_mod!(i128);

    typed_mod!(f64);

    #[cfg(test)]
    mod test_floats_exact {
        macro_rules! test_float_type_exact {
            ( $T:ident, $tname:ident ) => {
                #[test]
                fn $tname() {
                    assert_eq!(super::$T::IOTA.fract(), 0.0);

                    assert_eq!(super::$T::NANOMETER.fract(), 0.0);
                    assert_eq!(super::$T::MICROMETER.fract(), 0.0);
                    assert_eq!(super::$T::MILLIMETER.fract(), 0.0);
                    assert_eq!(super::$T::QUARTER_MILLIMETER.fract(), 0.0);
                    assert_eq!(super::$T::CENTIMETER.fract(), 0.0);
                    assert_eq!(super::$T::DECIMETER.fract(), 0.0);
                    assert_eq!(super::$T::METER.fract(), 0.0);

                    assert_eq!(super::$T::SIXTY_FOURTH.fract(), 0.0);
                    assert_eq!(super::$T::THIRTY_SECOND.fract(), 0.0);
                    assert_eq!(super::$T::SIXTEENTH.fract(), 0.0);
                    assert_eq!(super::$T::EIGHTH.fract(), 0.0);
                    assert_eq!(super::$T::QUARTER.fract(), 0.0);
                    assert_eq!(super::$T::HALF.fract(), 0.0);
                    assert_eq!(super::$T::HUNDRED_THOUSANDTH.fract(), 0.0);
                    assert_eq!(super::$T::TEN_THOUSANDTH.fract(), 0.0);
                    assert_eq!(super::$T::THOU.fract(), 0.0);
                    assert_eq!(super::$T::POINT.fract(), 0.0);
                    assert_eq!(super::$T::PICA.fract(), 0.0);
                    assert_eq!(super::$T::INCH.fract(), 0.0);
                    assert_eq!(super::$T::FOOT.fract(), 0.0);
                    assert_eq!(super::$T::YARD.fract(), 0.0);
                }
            };
        }

        test_float_type_exact!(f64, exact_f64);
    }
}

/// Per-target-type modules for units of mass denominated in ‘whit’ ― 1⁄3200 µg increments.
///
/// Unit chosen to express practically measurable weights (down to the 0.1 µg range) as well
/// as all common fractional denominations of the international pound (ounces, dram, thousandths of
/// an ounce, grains) and units related to the pound by grains (such as the troy ounce).
///
/// # Type selection
///
/// [`i64`](mass::i64) is sufficient to express masses and mass differences ± 2 882 303 kg or
/// ± 6 354 392 lb, so if your quantities exceed that, consider working in [`i128`](mass::i128).
pub mod mass {
    macro_rules! typed_mod {
        ( $T:ident ) => {
            /// Constants for common units of mass.
            pub mod $T {
                /// Whit ― 1⁄3200 µg.
                ///
                /// This allows common divisions of a [`POUND`] ([`OUNCE`], [`DRAM`],
                /// [`THOUSANDTH_OUNCE`]) and tenths of a [`MICROGRAM`] to be represented
                /// interchangeably as integers.
                ///
                /// Using this base unit, combinations of masses in either [US customary units] or
                /// [SI units] can be added, subtracted, multiplied, and often divided without loss.
                ///
                /// [US customary units]: <https://en.wikipedia.org/wiki/United_States_customary_units>
                /// [SI units]: <https://en.wikipedia.org/wiki/International_System_of_Units>
                pub const WHIT: $T = 1 as $T;

                /// Microgram.
                pub const MICROGRAM: $T = 3_200 as $T * WHIT;
                /// Milligram.
                pub const MILLIGRAM: $T = 1_000 as $T * MICROGRAM;
                /// Gram.
                pub const GRAM: $T = 1_000 as $T * MILLIGRAM;
                /// Kilogram.
                pub const KILOGRAM: $T = 1_000 as $T * GRAM;
                /// Megagram ― tonne/metric ton.
                ///
                /// Use this for SI tonnes instead of [`SHORT_TON`] and [`LONG_TON`].
                #[doc(alias = "METRIC_TON")]
                #[doc(alias = "TONNE")]
                pub const MEGAGRAM: $T = 1_000 as $T * KILOGRAM;

                /// Dram ― exactly 1⁄16 [`OUNCE`].
                pub const DRAM: $T = 5_669_904_625u64 as $T * WHIT;
                /// Ounce ― exactly 1⁄16 [`POUND`].
                pub const OUNCE: $T = 16 as $T * DRAM;
                /// Pound ― as defined in the [International Yard and Pound agreement].
                ///
                /// [International Yard and Pound agreement]: <https://en.wikipedia.org/wiki/International_yard_and_pound>
                pub const POUND: $T = 16 as $T * OUNCE;
                /// Stone ― exactly 14 [`POUND`].
                pub const STONE: $T = 14 as $T * POUND;
                /// Long hundredweight ― exactly 8 [`STONE`] or 112 [`POUND`].
                pub const LONG_HUNDREDWEIGHT: $T = 8 as $T * STONE;
                /// Long ton ― exactly 20 [`LONG_HUNDREDWEIGHT`].
                pub const LONG_TON: $T = 20 as $T * LONG_HUNDREDWEIGHT;
                /// Short hundredweight ― exactly 100 [`POUND`].
                pub const SHORT_HUNDREDWEIGHT: $T = 100 as $T * POUND;
                /// Short ton ― exactly 20 [`SHORT_HUNDREDWEIGHT`].
                pub const SHORT_TON: $T = 20 as $T * SHORT_HUNDREDWEIGHT;
                /// 1⁄1000 [`OUNCE`].
                pub const THOUSANDTH_OUNCE: $T = 90_718_474 as $T * WHIT;
                /// Grain ― exactly 1⁄7000 [`POUND`].
                pub const GRAIN: $T = 207_356_512 as $T * WHIT;
                /// Pennyweight ― exactly 24 [`GRAIN`].
                pub const PENNYWEIGHT: $T = 24 as $T * GRAIN;
                /// Troy ounce ― exactly 20 [`PENNYWEIGHT`] or 480 [`GRAIN`].
                pub const TROY_OUNCE: $T = 20 as $T * PENNYWEIGHT;
            }
        };
    }

    typed_mod!(i64);
    typed_mod!(u64);

    typed_mod!(u128);
    typed_mod!(i128);

    typed_mod!(f64);

    #[cfg(test)]
    mod test_floats_exact {
        macro_rules! test_float_type_exact {
            ( $T:ident, $tname:ident ) => {
                #[test]
                fn $tname() {
                    assert_eq!(super::$T::WHIT.fract(), 0.0);

                    assert_eq!(super::$T::MICROGRAM.fract(), 0.0);
                    assert_eq!(super::$T::MILLIGRAM.fract(), 0.0);
                    assert_eq!(super::$T::GRAM.fract(), 0.0);
                    assert_eq!(super::$T::KILOGRAM.fract(), 0.0);
                    assert_eq!(super::$T::MEGAGRAM.fract(), 0.0);

                    assert_eq!(super::$T::DRAM.fract(), 0.0);
                    assert_eq!(super::$T::OUNCE.fract(), 0.0);
                    assert_eq!(super::$T::POUND.fract(), 0.0);
                    assert_eq!(super::$T::STONE.fract(), 0.0);
                    assert_eq!(super::$T::LONG_HUNDREDWEIGHT.fract(), 0.0);
                    assert_eq!(super::$T::LONG_TON.fract(), 0.0);
                    assert_eq!(super::$T::SHORT_HUNDREDWEIGHT.fract(), 0.0);
                    assert_eq!(super::$T::SHORT_TON.fract(), 0.0);
                    assert_eq!(super::$T::THOUSANDTH_OUNCE.fract(), 0.0);
                    assert_eq!(super::$T::GRAIN.fract(), 0.0);
                    assert_eq!(super::$T::PENNYWEIGHT.fract(), 0.0);
                    assert_eq!(super::$T::TROY_OUNCE.fract(), 0.0);
                }
            };
        }

        test_float_type_exact!(f64, exact_f64);
    }
}

/// Per-target-type modules for units of temperature denominated in ‘smidge’ ― 1⁄90 mK increments.
///
/// Represents temperatures down to the 100 µK/0.0001 °R range, which is sufficient for
/// almost all practical thermometry. This also allows you to exactly represent temperatures used in
/// industrial metrology standards such as [ITS-90] for fixed points and common derived constants,
/// and allows exact interchange between common absolute (Kelvin/[Rankine]) and relative
/// (Celsius/Fahrenheit) temperature scales.
///
/// # Type selection
///
/// [`i32`](temperature::i32) is sufficient for absolute temperatures and differences ± 23 860 K
/// or ± 42 949 °R.
///
/// [ITS-90]: <https://en.wikipedia.org/wiki/International_Temperature_Scale_of_1990>
/// [Rankine]: <https://en.wikipedia.org/wiki/Rankine_scale>
pub mod temperature {
    macro_rules! typed_mod {
        ( $T:ident ) => {
            /// Constants for common units of temperature.
            pub mod $T {
                /// Smidge ― 1⁄90 mK.
                ///
                /// This allows 0.1 mK and 0.1 °R and their common multiples to be represented
                /// interchangeably as integers.
                ///
                /// To operate on relative scales (Celsius, Fahrenheit), make sure to account for
                /// the difference in origin points with [`ZERO_CELSIUS`] and [`ZERO_FAHRENHEIT`].
                ///
                /// The value 1⁄90 mK was chosen rather than 1⁄9 because ITS-90 defines fixed points
                /// to four decimal digits, making some standard temperatures representable with
                /// 100 µK precision, but not with 1 mK precision.
                ///
                /// Using this base unit, combinations of temperatures in [US customary units] or
                /// [SI units] can be added, subtracted, multiplied, and often divided without loss.
                ///
                /// [US customary units]: <https://en.wikipedia.org/wiki/United_States_customary_units>
                /// [SI units]: <https://en.wikipedia.org/wiki/International_System_of_Units>
                pub const SMIDGE: $T = 1 as $T;

                /// Millikelvin.
                pub const MILLIKELVIN: $T = 90 as $T * SMIDGE;
                /// Kelvin ― absolute scale of Celsius.
                ///
                /// Use this as the increment of Celsius temperatures, where
                /// e.g. 10 C = [`ZERO_CELSIUS`] + 10 × [`KELVIN`].
                ///
                /// Only the absolute form is given here, to avoid confusion due to Celsius not
                /// starting at absolute zero.
                #[doc(alias = "CELSIUS_INCREMENT")]
                pub const KELVIN: $T = 1_000 as $T * MILLIKELVIN;
                /// 0°C ― exactly 273.15 [`KELVIN`].
                ///
                /// [`ZERO_CELSIUS`] is also exactly [`ZERO_FAHRENHEIT`] + 32 × [`RANKINE`].
                pub const ZERO_CELSIUS: $T = 273_150 as $T * MILLIKELVIN;

                /// 1⁄1000 Rankine.
                pub const THOUSANDTH_RANKINE: $T = 50 as $T * SMIDGE;
                /// Rankine ― absolute scale of Fahrenheit.
                ///
                /// Use this as the increment of Fahrenheit temperatures, where
                /// e.g. 50 F = [`ZERO_FAHRENHEIT`] + 50 × [`RANKINE`].
                ///
                /// Only the absolute form is given here, to avoid confusion due to Fahrenheit not
                /// starting at absolute zero.
                #[doc(alias = "FAHRENHEIT_INCREMENT")]
                pub const RANKINE: $T = 1_000 as $T * THOUSANDTH_RANKINE;
                /// 0°F ― exactly 459 670 [`THOUSANDTH_RANKINE`].
                pub const ZERO_FAHRENHEIT: $T = 459_670 as $T * THOUSANDTH_RANKINE;
            }
        };
    }

    typed_mod!(i32);
    typed_mod!(u32);

    typed_mod!(i64);
    typed_mod!(u64);

    typed_mod!(u128);
    typed_mod!(i128);

    typed_mod!(f64);

    #[cfg(test)]
    mod test_floats_exact {
        macro_rules! test_float_type_exact {
            ( $T:ident, $tname:ident ) => {
                #[test]
                fn $tname() {
                    assert_eq!(super::$T::SMIDGE.fract(), 0.0);

                    assert_eq!(super::$T::MILLIKELVIN.fract(), 0.0);
                    assert_eq!(super::$T::KELVIN.fract(), 0.0);
                    assert_eq!(super::$T::ZERO_CELSIUS.fract(), 0.0);

                    assert_eq!(super::$T::THOUSANDTH_RANKINE.fract(), 0.0);
                    assert_eq!(super::$T::RANKINE.fract(), 0.0);
                    assert_eq!(super::$T::ZERO_FAHRENHEIT.fract(), 0.0);
                }
            };
        }

        test_float_type_exact!(f64, exact_f64);
    }
}
