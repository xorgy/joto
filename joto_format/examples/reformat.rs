// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Debug CLI for [`joto_parse`] and [`joto_format`].

use std::env;

use joto_format::length::i128::format_dim;
use joto_format::length::{FootInchMode, LengthFormat};
use joto_format::OutputDeviceMode;
use joto_parse::i128::parse_dim_diagnostic;
use joto_parse::{strip_unit, Unit};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Box<[String]> = env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!(
            "Usage: reformat <dimension> [--as <unit>] [--ascii | --complex] [--mixed-prefer-fraction | --mixed-prefer-decimal | --single-unit-prefer-fraction | --single-unit-prefer-decimal | --single-unit-fraction-only | --single-unit-decimal-only]"
        );
        return Ok(());
    }

    let dimension = &args[0];
    let (_, parsed_unit) = strip_unit(dimension.trim()).unwrap_or(("", Unit::Iota));
    let mut output_unit = parsed_unit;

    let mut output_format = LengthFormat::default();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--as" => {
                i += 1;
                if i >= args.len() {
                    return Err("Missing unit for --as".into());
                }
                let (_, unit) = strip_unit(&args[i]).ok_or("Invalid unit for --as")?;
                output_unit = unit;
                i += 1;
            }
            "--ascii" => {
                output_format.output_device_mode = OutputDeviceMode::Ascii;
                i += 1;
            }
            "--complex" => {
                output_format.output_device_mode = OutputDeviceMode::Complex;
                i += 1;
            }
            "--mixed-prefer-fraction" => {
                output_format.foot_inch_mode = FootInchMode::MixedPreferFraction;
                i += 1;
            }
            "--mixed-prefer-decimal" => {
                output_format.foot_inch_mode = FootInchMode::MixedPreferDecimal;
                i += 1;
            }
            "--single-unit-prefer-fraction" => {
                output_format.foot_inch_mode = FootInchMode::SingleUnitPreferFraction;
                i += 1;
            }
            "--single-unit-prefer-decimal" => {
                output_format.foot_inch_mode = FootInchMode::SingleUnitPreferDecimal;
                i += 1;
            }
            "--single-unit-fraction-only" => {
                output_format.foot_inch_mode = FootInchMode::SingleUnitFractionOnly;
                i += 1;
            }
            "--single-unit-decimal-only" => {
                output_format.foot_inch_mode = FootInchMode::SingleUnitDecimalOnly;
                i += 1;
            }
            _ => {
                return Err(format!("Unknown flag: {}", args[i]).into());
            }
        }
    }

    let quantity = match parse_dim_diagnostic(dimension) {
        Ok(quantity) => {
            if matches!(
                dimension.trim_start().as_bytes(),
                [b'-', ..] | [0xE2, 0x88, 0x92, ..]
            ) {
                -quantity
            } else {
                quantity
            }
        }
        Err(e) => {
            return Err(format!("Failed to parse {dimension:?}: {e:#?}").into());
        }
    };

    let formatted = format_dim(quantity, output_unit, output_format);
    let eqsign = if formatted.exact {
        "="
    } else {
        match output_format.output_device_mode {
            OutputDeviceMode::Ascii => "~",
            OutputDeviceMode::Complex => "≈",
        }
    };
    println!("{eqsign} {}", formatted.as_ref());

    Ok(())
}
