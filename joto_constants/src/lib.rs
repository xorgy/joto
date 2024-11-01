// Copyright 2024 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Constants for interoperation with Joto workspace packages.

#![no_std]

macro_rules! typed_mod {
    ( $T:ident ) => {
        /// Constants for common units of length.
        pub mod $T {
            /// One ninth of a nanometer.
            ///
            /// This allows common fractions of an inch ([`TEN_THOUSANDTH`], [`POINT`], [`SIXTY_FOURTH`])
            /// and [`NANOMETER`] to be represented as integers.
            /// Using this base unit, combinations of lengths in either
            /// [US customary Units](<https://en.wikipedia.org/wiki/United_States_customary_units>) or
            /// [SI units](<https://en.wikipedia.org/wiki/International_System_of_Units>) can be added,
            /// subtracted, and multiplied without loss of precision.
            pub const IOTA: $T = 1 as $T;
            /// One nanometer.
            pub const NANOMETER: $T = 9 as $T * IOTA;
            /// One micrometer.
            pub const MICROMETER: $T = 1_000 as $T * NANOMETER;
            /// One millimeter.
            pub const MILLIMETER: $T = 1_000 as $T * MICROMETER;
            /// One centimeter.
            pub const CENTIMETER: $T = 10 as $T * MILLIMETER;
            /// One meter.
            pub const METER: $T = 1_000 as $T * MILLIMETER;

            /// 1⁄64 of an [`INCH`].
            pub const SIXTY_FOURTH: $T = 3_571_875 as $T * IOTA;
            /// 1⁄32 of an [`INCH`].
            pub const THIRTY_SECOND: $T = 2 as $T * SIXTY_FOURTH;
            /// 1⁄16 of an [`INCH`].
            pub const SIXTEENTH: $T = 2 as $T * THIRTY_SECOND;
            /// 1⁄8 of an [`INCH`].
            pub const EIGHTH: $T = 2 as $T * SIXTEENTH;
            /// 1⁄4 of an [`INCH`].
            pub const QUARTER: $T = 2 as $T * EIGHTH;
            /// 1⁄2 of an [`INCH`].
            pub const HALF: $T = 2 as $T * QUARTER;
            /// 1⁄10000 of an [`INCH`].
            pub const TEN_THOUSANDTH: $T = 22_860 as $T * IOTA;
            /// 1⁄1000 of an [`INCH`].
            pub const THOU: $T = 10 as $T * TEN_THOUSANDTH;
            /// One [desktop publishing point](<https://en.wikipedia.org/wiki/Point_(typography)#Desktop_publishing_point>).
            ///
            /// Exactly 1⁄72 of an [`INCH`] or 1⁄12 of a [`PICA`].
            pub const POINT: $T = 3_175_000 as $T * IOTA;
            /// One pica.
            ///
            /// Exactly 1⁄6 of an [`INCH`] or 12 [`POINT`].
            pub const PICA: $T = 12 as $T * POINT;
            /// One inch.
            ///
            /// Exactly 1⁄12 of a [`FOOT`].
            pub const INCH: $T = 6 as $T * PICA;
            /// One foot.
            ///
            /// Exactly 1⁄3 of a [`YARD`].
            pub const FOOT: $T = 12 as $T * INCH;
            /// One yard, as defined in the [International Yard and Pound agreement](<https://en.wikipedia.org/wiki/International_yard_and_pound>).
            pub const YARD: $T = 3 as $T * FOOT;
        }
    };
}

typed_mod!(i64);
typed_mod!(u64);

typed_mod!(u128);
typed_mod!(i128);

typed_mod!(f32);
typed_mod!(f64);

#[cfg(test)]
mod test_floats_exact {
    macro_rules! test_float_type_exact {
        ( $T:ident, $tname:ident ) => {
            #[test]
            fn $tname() {
                assert_eq!(crate::$T::IOTA.fract(), 0.0);
                assert_eq!(crate::$T::NANOMETER.fract(), 0.0);
                assert_eq!(crate::$T::MICROMETER.fract(), 0.0);
                assert_eq!(crate::$T::MILLIMETER.fract(), 0.0);
                assert_eq!(crate::$T::CENTIMETER.fract(), 0.0);
                assert_eq!(crate::$T::METER.fract(), 0.0);

                assert_eq!(crate::$T::SIXTY_FOURTH.fract(), 0.0);
                assert_eq!(crate::$T::THIRTY_SECOND.fract(), 0.0);
                assert_eq!(crate::$T::SIXTEENTH.fract(), 0.0);
                assert_eq!(crate::$T::EIGHTH.fract(), 0.0);
                assert_eq!(crate::$T::QUARTER.fract(), 0.0);
                assert_eq!(crate::$T::HALF.fract(), 0.0);
                assert_eq!(crate::$T::TEN_THOUSANDTH.fract(), 0.0);
                assert_eq!(crate::$T::THOU.fract(), 0.0);
                assert_eq!(crate::$T::POINT.fract(), 0.0);
                assert_eq!(crate::$T::PICA.fract(), 0.0);
                assert_eq!(crate::$T::INCH.fract(), 0.0);
                assert_eq!(crate::$T::FOOT.fract(), 0.0);
                assert_eq!(crate::$T::YARD.fract(), 0.0);
            }
        };
    }

    test_float_type_exact!(f64, exact_f64);
    test_float_type_exact!(f32, exact_f32);
}
