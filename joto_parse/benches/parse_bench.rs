// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

#[cfg(not(target_arch = "wasm32"))]
use divan::{
    counter::{BytesCount, ItemsCount},
    main, Bencher,
};

macro_rules! bench_function {
    ( $S:expr, $T:ident ) => {
        #[divan::bench]
        fn $T(bencher: Bencher) {
            bencher.with_inputs(|| $S.to_owned()).bench_refs(|s| {
                use joto_parse::length::$T::parse_dim;
                parse_dim(s.as_ref()).unwrap()
            });
        }
    };
}

macro_rules! bench_mass_function {
    ( $S:expr, $T:ident ) => {
        #[divan::bench]
        fn $T(bencher: Bencher) {
            bencher.with_inputs(|| $S.to_owned()).bench_refs(|s| {
                use joto_parse::mass::$T::parse_dim;
                parse_dim(s.as_ref()).unwrap()
            });
        }
    };
}

macro_rules! bench_temperature_function {
    ( $S:expr, $T:ident ) => {
        #[divan::bench]
        fn $T(bencher: Bencher) {
            bencher.with_inputs(|| $S.to_owned()).bench_refs(|s| {
                use joto_parse::temperature::$T::parse_dim;
                parse_dim(s.as_ref()).unwrap()
            });
        }
    };
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse: \"32′11﻿1⁄4″\"")]
mod quite_simple {
    use super::*;

    const S: &str = "32′11﻿1⁄4″";

    bench_function!(S, u64);
    bench_function!(S, i64);
    bench_function!(S, u128);
    bench_function!(S, i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse: \"20m\"")]
mod very_simple {
    use super::*;

    const S: &str = "20m";

    bench_function!(S, u64);
    bench_function!(S, i64);
    bench_function!(S, u128);
    bench_function!(S, i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse: \"  34,966' 11 1⁄4\"  \"")]
mod kinda_rough {
    use super::*;

    const S: &str = "  34,966' 11 1⁄4\"  ";

    bench_function!(S, u64);
    bench_function!(S, i64);
    bench_function!(S, u128);
    bench_function!(S, i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse mass: \"5lb 3oz\"")]
mod mass_quite_simple {
    use super::*;

    const S: &str = "5lb 3oz";

    bench_mass_function!(S, u64);
    bench_mass_function!(S, i64);
    bench_mass_function!(S, u128);
    bench_mass_function!(S, i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse mass: \"20kg\"")]
mod mass_very_simple {
    use super::*;

    const S: &str = "20kg";

    bench_mass_function!(S, u64);
    bench_mass_function!(S, i64);
    bench_mass_function!(S, u128);
    bench_mass_function!(S, i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse temperature: \"100°C\"")]
mod temperature_quite_simple {
    use super::*;

    const S: &str = "100°C";

    bench_temperature_function!(S, u32);
    bench_temperature_function!(S, i32);
    bench_temperature_function!(S, u64);
    bench_temperature_function!(S, i64);
    bench_temperature_function!(S, u128);
    bench_temperature_function!(S, i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse temperature: \"273.15K\"")]
mod temperature_very_simple {
    use super::*;

    const S: &str = "273.15K";

    bench_temperature_function!(S, u32);
    bench_temperature_function!(S, i32);
    bench_temperature_function!(S, u64);
    bench_temperature_function!(S, i64);
    bench_temperature_function!(S, u128);
    bench_temperature_function!(S, i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse temperature: \"-459.67°F\"")]
mod temperature_negative_fahrenheit {
    use super::*;

    const S: &str = "-459.67°F";

    bench_temperature_function!(S, u32);
    bench_temperature_function!(S, i32);
    bench_temperature_function!(S, u64);
    bench_temperature_function!(S, i64);
    bench_temperature_function!(S, u128);
    bench_temperature_function!(S, i128);
}

macro_rules! bench_inch_function {
    ( $S:expr, $T:ident ) => {
        #[divan::bench]
        fn $T(bencher: Bencher) {
            bencher.with_inputs(|| $S.to_owned()).bench_refs(|s| {
                use joto_parse::length::$T::parse_as;
                parse_as(s.as_ref(), joto_parse::length::Unit::Inch).unwrap()
            });
        }
    };
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Parse: \"176\" as Inch")]
mod simple_as {
    use super::*;

    const S: &str = "176";

    bench_inch_function!(S, u64);
    bench_inch_function!(S, i64);
    bench_inch_function!(S, u128);
    bench_inch_function!(S, i128);
}

const EXAMPLES: [&str; 48] = [
    // Inches
    "3in",
    "12.7in",
    "1/2\"",
    "2ft 3in",
    "1.25in",
    "1 203.5in", // narrow no-break space thousands sep
    // Feet
    "5ft",
    "5'11\"",
    "1.5ft",
    "0.25ft",
    "12′", // prime
    // Yards
    "3yd",
    "2.5yd",
    "0.1yd",
    // Nanometers
    "500nm",
    "0.0005nm",
    "123456789nm",
    // Micrometers
    "10um",
    "1µm",
    "0.5µm",
    "0.75μm", // Greek mu
    // Millimeters
    "3mm",
    "30.5mm",
    "999,999mm",
    // Centimeters
    "25cm",
    "2.54cm",
    "0.1cm",
    // Decimeters
    "45dm",
    "1.5dm",
    // Meters
    "1m",
    "0.002m",
    "4m 3mm",
    // Q
    "0.25Q",
    "12Q",
    // Points
    "12pt",
    "8.5pt",
    // Picas
    "6pc",
    "2.5pc",
    // Iota
    "10io",
    "0.1io",
    // And now for some hideous ones
    "12,345,678.9012m",
    "9223372036854775807nm", // i64::MAX in nm
    "1.0000000000100000000000000000000000000000m",
    "4' 11  7/16\"",
    "1,234,567ft 8.999in",
    // Many U+2008 Punctuation Space thousands separators.
    "999\u{2008}999\u{2008}999\u{2008}999\u{2008}999\u{2008}999\u{2008}999\u{2008}999\u{2008}999\u{2008}999.9999mm",
    "1234567890.12345Q",
    "18446744073709551615io",
];

const EXAMPLES_BYTES_TOTAL: usize = {
    let mut t = 0;
    let mut i = EXAMPLES.len();
    while i > 0 {
        i -= 1;
        t += EXAMPLES[i].len();
    }
    t
};

const MASS_EXAMPLES: [&str; 32] = [
    "1g",
    "1mg",
    "1ug",
    "1µg",
    "1μg",
    "1kg",
    "1t",
    "0.5kg",
    "0.001oz",
    "1oz",
    "5lb",
    "5lb 3oz",
    "12oz",
    "0.1ozt",
    "1ozt",
    "5dr",
    "12dwt",
    "2gr",
    "1,000g",
    // Many U+2008 Punctuation Space thousands separators.
    "999\u{2008}999\u{2008}999g",
    "12,345,678.901234kg",
    "18446744073709551615wt",
    "0.01ug",
    "0.00001mg",
    "1.000oz",
    "1.0000kg",
    "9223372036854775807ug",
    "1kg 1oz", // invalid compound, should yield None
    "3.141592653589793t",
    "100cwt",
    "1cwt.l",
    "1tn.l",
];

const MASS_EXAMPLES_BYTES_TOTAL: usize = {
    let mut t = 0;
    let mut i = MASS_EXAMPLES.len();
    while i > 0 {
        i -= 1;
        t += MASS_EXAMPLES[i].len();
    }
    t
};

const TEMP_EXAMPLES: [&str; 32] = [
    "0K",
    "273.15K",
    "300K",
    "0°C",
    "25°C",
    "-10°C",
    "32°F",
    "212°F",
    "459.67°R",
    "491.67°R",
    "0R",
    "1mK",
    "0.1mK",
    ".0001K",
    ".0001°C",
    ".0001°F",
    "1mR",
    ".1mR",
    ".0001R",
    "1,000K",
    "999\u{2008}999mK",
    "23\u{2008}860K",
    "23,860K",
    "100sd",
    "1smidge",
    "+10K",
    "\u{2212}10°F",
    "0.0000K",
    "0.0000°C",
    // Should yield None for unsigned types.
    "-1K",
    "-9999999999999999999999999999999999999K",
    // Too precise.
    "0.00001K",
];

const TEMP_EXAMPLES_BYTES_TOTAL: usize = {
    let mut t = 0;
    let mut i = TEMP_EXAMPLES.len();
    while i > 0 {
        i -= 1;
        t += TEMP_EXAMPLES[i].len();
    }
    t
};

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "48 strings, 8 degenerates, shuffled per iteration.")]
mod variety {
    use super::*;
    use rand::{rng, rngs::SmallRng, seq::SliceRandom, SeedableRng};

    macro_rules! bench_function_array {
        ( $T:ident ) => {
            #[divan::bench]
            fn $T(bencher: Bencher) {
                let items = ItemsCount::new(EXAMPLES.len());
                let bytes = BytesCount::new(EXAMPLES_BYTES_TOTAL);
                bencher
                    .with_inputs(|| {
                        let mut r = SmallRng::from_rng(&mut rng());
                        let mut y: [&'static str; 48] = EXAMPLES;
                        y.shuffle(&mut r);
                        y
                    })
                    .counter(items)
                    .counter(bytes)
                    .bench_values(|ss| {
                        use joto_parse::length::$T::parse_dim;
                        let mut o: [$T; 48] = [0; 48];
                        for (i, &s) in ss.iter().enumerate() {
                            if let Some(v) = parse_dim(s) {
                                o[i] = v;
                            }
                        }
                        o
                    });
            }
        };
    }

    bench_function_array!(u64);
    bench_function_array!(i64);
    bench_function_array!(u128);
    bench_function_array!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Mass: 32 strings, shuffled per iteration.")]
mod mass_variety {
    use super::*;
    use rand::{rng, rngs::SmallRng, seq::SliceRandom, SeedableRng};

    macro_rules! bench_function_array {
        ( $T:ident ) => {
            #[divan::bench]
            fn $T(bencher: Bencher) {
                let items = ItemsCount::new(MASS_EXAMPLES.len());
                let bytes = BytesCount::new(MASS_EXAMPLES_BYTES_TOTAL);
                bencher
                    .with_inputs(|| {
                        let mut r = SmallRng::from_rng(&mut rng());
                        let mut y: [&'static str; 32] = MASS_EXAMPLES;
                        y.shuffle(&mut r);
                        y
                    })
                    .counter(items)
                    .counter(bytes)
                    .bench_values(|ss| {
                        use joto_parse::mass::$T::parse_dim;
                        let mut o: [$T; 32] = [0; 32];
                        for (i, &s) in ss.iter().enumerate() {
                            if let Some(v) = parse_dim(s) {
                                o[i] = v;
                            }
                        }
                        o
                    });
            }
        };
    }

    bench_function_array!(u64);
    bench_function_array!(i64);
    bench_function_array!(u128);
    bench_function_array!(i128);
}

#[cfg(not(target_arch = "wasm32"))]
#[divan::bench_group(name = "Temperature: 32 strings, shuffled per iteration.")]
mod temperature_variety {
    use super::*;
    use rand::{rng, rngs::SmallRng, seq::SliceRandom, SeedableRng};

    macro_rules! bench_function_array {
        ( $T:ident ) => {
            #[divan::bench]
            fn $T(bencher: Bencher) {
                let items = ItemsCount::new(TEMP_EXAMPLES.len());
                let bytes = BytesCount::new(TEMP_EXAMPLES_BYTES_TOTAL);
                bencher
                    .with_inputs(|| {
                        let mut r = SmallRng::from_rng(&mut rng());
                        let mut y: [&'static str; 32] = TEMP_EXAMPLES;
                        y.shuffle(&mut r);
                        y
                    })
                    .counter(items)
                    .counter(bytes)
                    .bench_values(|ss| {
                        use joto_parse::temperature::$T::parse_dim;
                        let mut o: [$T; 32] = [0; 32];
                        for (i, &s) in ss.iter().enumerate() {
                            if let Some(v) = parse_dim(s) {
                                o[i] = v;
                            }
                        }
                        o
                    });
            }
        };
    }

    bench_function_array!(u32);
    bench_function_array!(i32);
    bench_function_array!(u64);
    bench_function_array!(i64);
    bench_function_array!(u128);
    bench_function_array!(i128);
}
