// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

#[cfg(not(target_arch = "wasm32"))]
use divan::{main, Bencher};

macro_rules! bench_length_format_function {
    ( $T:ident, $Q:expr, $UNIT:expr, $F:expr ) => {
        #[divan::bench]
        fn $T(bencher: Bencher) {
            bencher.with_inputs(|| $Q).bench_refs(|q| {
                use joto_format::length::$T::format_dim;
                format_dim(*q, $UNIT, $F)
            });
        }
    };
}

macro_rules! bench_mass_format_function {
    ( $T:ident, $Q:expr, $UNIT:expr, $F:expr ) => {
        #[divan::bench]
        fn $T(bencher: Bencher) {
            bencher.with_inputs(|| $Q).bench_refs(|q| {
                use joto_format::mass::$T::format_dim;
                format_dim(*q, $UNIT, $F)
            });
        }
    };
}

macro_rules! bench_temperature_format_function {
    ( $T:ident, $Q:expr, $UNIT:expr, $F:expr ) => {
        #[divan::bench]
        fn $T(bencher: Bencher) {
            bencher.with_inputs(|| $Q).bench_refs(|q| {
                use joto_format::temperature::$T::format_dim;
                format_dim(*q, $UNIT, $F)
            });
        }
    };
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format length: \"20m\"")]
mod length_very_simple {
    use super::*;

    use joto_format::length::{LengthFormat, Unit};

    const F: LengthFormat = LengthFormat::new();

    macro_rules! bench {
        ( $T:ident ) => {
            bench_length_format_function!(
                $T,
                20 * joto_constants::length::$T::METER,
                Unit::Meter,
                F
            );
        };
    }

    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format length: \"32′11﻿1⁄4″\"")]
mod length_fractional_compound {
    use super::*;

    use joto_format::length::{FracType, LengthFormat, Unit};
    use joto_format::OutputDeviceMode;

    const F: LengthFormat = LengthFormat {
        max_decimal_fraction_digits: None,
        thousands_separator: None,
        frac_type: FracType::Whole,
        allow_frac_fallback: true,
        mixed: true,
        output_device_mode: OutputDeviceMode::Complex,
    };

    macro_rules! bench {
        ( $T:ident ) => {
            bench_length_format_function!(
                $T,
                32 * joto_constants::length::$T::FOOT
                    + 11 * joto_constants::length::$T::INCH
                    + 16 * joto_constants::length::$T::SIXTY_FOURTH,
                Unit::Foot,
                F
            );
        };
    }

    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format mass: \"20kg\"")]
mod mass_very_simple {
    use super::*;

    use joto_format::mass::{MassFormat, Unit};

    const F: MassFormat = MassFormat::new();

    macro_rules! bench {
        ( $T:ident ) => {
            bench_mass_format_function!(
                $T,
                20 * joto_constants::mass::$T::KILOGRAM,
                Unit::Kilogram,
                F
            );
        };
    }

    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format mass: \"1.00000000000001t\"")]
mod mass_long_decimal {
    use super::*;

    use joto_format::mass::{MassFormat, Unit};

    const F: MassFormat = MassFormat::new();

    macro_rules! bench {
        ( $T:ident ) => {
            bench_mass_format_function!(
                $T,
                joto_constants::mass::$T::MEGAGRAM
                    + joto_constants::mass::$T::MEGAGRAM / 100_000_000_000_000,
                Unit::Megagram,
                F
            );
        };
    }

    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format temperature: \"273.15K\"")]
mod temperature_quite_simple {
    use super::*;

    use joto_format::temperature::{TemperatureFormat, Unit};

    const F: TemperatureFormat = TemperatureFormat::new();

    macro_rules! bench {
        ( $T:ident ) => {
            bench_temperature_format_function!(
                $T,
                273 * joto_constants::temperature::$T::KELVIN
                    + 150 * joto_constants::temperature::$T::MILLIKELVIN,
                Unit::Kelvin,
                F
            );
        };
    }

    bench!(u32);
    bench!(i32);
    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format temperature: \"-459.67°F\"")]
mod temperature_negative_fahrenheit {
    use super::*;

    use joto_format::temperature::{TemperatureFormat, Unit};

    const F: TemperatureFormat = TemperatureFormat::new();

    macro_rules! bench {
        ( $T:ident ) => {
            bench_temperature_format_function!($T, 0 as $T, Unit::Fahrenheit, F);
        };
    }

    bench!(u32);
    bench!(i32);
    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format temperature: \"0.0001K\"")]
mod temperature_small_kelvin {
    use super::*;

    use joto_format::temperature::{TemperatureFormat, Unit};

    const F: TemperatureFormat = TemperatureFormat::new();

    macro_rules! bench {
        ( $T:ident ) => {
            bench_temperature_format_function!(
                $T,
                joto_constants::temperature::$T::KELVIN / 10_000,
                Unit::Kelvin,
                F
            );
        };
    }

    bench!(u32);
    bench!(i32);
    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Format length: \"12,345,678.9012m\"")]
mod length_decimal_separated {
    use super::*;

    use joto_format::length::{LengthFormat, Unit};

    const F: LengthFormat = LengthFormat {
        max_decimal_fraction_digits: None,
        thousands_separator: Some(','),
        ..LengthFormat::new()
    };

    macro_rules! bench {
        ( $T:ident ) => {
            bench_length_format_function!(
                $T,
                12_345_678 * joto_constants::length::$T::METER
                    + 901_200_000 * joto_constants::length::$T::NANOMETER,
                Unit::Meter,
                F
            );
        };
    }

    bench!(u64);
    bench!(i64);
    bench!(u128);
    bench!(i128);
}
