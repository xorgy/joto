// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

use joto_constants::i64::NANOMETER;
use joto_constants::u64::MICROMETER;
use joto_parse_macros::dim;

fn main() {
    // One advantage of the dim! macro is that it generates an unsuffixed integer literal
    // which can be interpreted as any integer type at compile time.
    let ambiguous_integer = dim!(31ft 7/32in);
    // So here when we divide it, by a unit constant, it gains a concrete type.
    println!(
        "{ambiguous_integer} iotas, or {}nm for `dim!(31ft 7/32in)`",
        ambiguous_integer / NANOMETER
    );

    const D1: u64 = dim!(21ft 11 1/2in);
    println!(
        "{D1} iotas, or {}µm for `dim!(21ft 11 1/2in)`",
        D1 / MICROMETER
    );

    const D2: i64 = dim!(31µm);
    println!("{D2} iotas, or {}nm for `dim!(31µm)`", D2 / NANOMETER);

    // Some dimension strings are only valid in a string literal.
    const D3: i128 = dim!("21′11﻿37⁄64″");
    println!(
        r#"{D3} iotas, or {}nm for `dim!("21′11﻿37⁄64″")`"#,
        D3 / NANOMETER as i128
    );

    // Some dimension strings are only valid in a string literal.
    const NEGATIVE_NELLY: i128 = -dim!("5′ 3 1⁄2″");
    println!(
        r#"{NEGATIVE_NELLY} iotas, or {}µm for `-dim!("5′ 3 1⁄2″")`"#,
        NEGATIVE_NELLY / MICROMETER as i128
    );
}
