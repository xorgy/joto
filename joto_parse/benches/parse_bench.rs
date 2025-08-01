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
                use joto_parse::$T::parse_dim;
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
                        use joto_parse::$T::parse_dim;
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
