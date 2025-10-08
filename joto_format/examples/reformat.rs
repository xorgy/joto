// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Dimension string reformatter using [`joto_parse`] and [`joto_format`], to explore round-trip conversion.

use std::env;
use std::process::ExitCode;

use joto_format::length::i128::format_dim;
use joto_format::length::{FracType, LengthFormat};
use joto_format::OutputDeviceMode;
use joto_parse::i128::parse_dim_diagnostic;
use joto_parse::{strip_unit, Unit};

const USAGE: &str = "Usage: reformat <dimension...> [--help] [--as <unit>] [--ascii | --complex ] [--prefer-fraction | --prefer-decimal] [--[no-]frac-fallback ] [--[no-]mixed ]";

const HELP: &str = "\
Reformat a dimension string into a specified unit and format.

Usage: reformat <dimension...> [options]

<dimension...>: One or more arguments forming a dimension string (e.g., '1 1/2 in' or '1' '1/2' 'in').

Options:
  --as <unit>              Output in the specified unit (e.g., 'm', 'in', 'ft'). Defaults to the input's unit.
  --ascii                  Output only ASCII characters (e.g., ' for ft, \" for in).
  --complex                Output Unicode characters (e.g., U+2032 for ft, U+2033 for in). Default.
  --prefer-fraction        Prefer whole number fractions (e.g. 37/64) for inches when possible.
  --prefer-decimal         Prefer decimal fractions (e.g., 0.5) for inches.
  --[no-]frac-fallback     Allow decimal fractions as a fallback if whole fractions are inexact. Default on.
  --[no-]mixed             Allow mixed units (e.g., feet and inches) in output. Default mixed units.
  --help, -h               Show this help message.
";

fn main() -> ExitCode {
    let mut args = env::args().skip(1).peekable();
    let Some(_) = args.peek() else {
        eprintln!("{USAGE}");
        return ExitCode::SUCCESS;
    };

    let mut dimension = String::new();
    let mut output_unit: Option<Unit> = None;
    let mut output_format = LengthFormat::default();

    while let Some(arg) = args.next() {
        match arg.as_ref() {
            "--help" | "-h" => {
                eprintln!("{HELP}");
                return ExitCode::SUCCESS;
            }
            "--as" => {
                if let Some(unit_str) = args.next() {
                    let Some(("", unit)) = strip_unit(&unit_str) else {
                        eprintln!("Invalid unit specification for --as: {unit_str}");
                        return ExitCode::FAILURE;
                    };
                    output_unit = Some(unit);
                } else {
                    eprintln!("Missing unit for --as");
                    return ExitCode::FAILURE;
                }
            }
            "--ascii" | "-a" => {
                output_format.output_device_mode = OutputDeviceMode::Ascii;
            }
            "--complex" | "-c" => {
                output_format.output_device_mode = OutputDeviceMode::Complex;
            }
            "--prefer-fraction" => {
                output_format.frac_type = FracType::Whole;
            }
            "--prefer-decimal" => {
                output_format.frac_type = FracType::Decimal;
            }
            "--no-mixed" => {
                output_format.mixed = false;
            }
            "--mixed" => {
                output_format.mixed = true;
            }
            "--no-frac-fallback" => {
                output_format.allow_frac_fallback = false;
            }
            "--frac-fallback" => {
                output_format.allow_frac_fallback = true;
            }
            arg if arg.starts_with("--") => {
                eprintln!("Unknown flag: {arg}");
                eprintln!("{USAGE}");
                return ExitCode::FAILURE;
            }
            arg => {
                // Collect contiguous non-flag arguments for dimension.
                dimension.push_str(arg);
                while !matches!(args.peek(), Some(next_arg) if next_arg.starts_with("--")) {
                    if let Some(next_arg) = args.next() {
                        dimension.push(' ');
                        dimension.push_str(&next_arg);
                    }
                }
            }
        }
    }

    if dimension.is_empty() {
        eprintln!("No dimension provided");
        return ExitCode::FAILURE;
    }

    let (_, parsed_unit) = strip_unit(&dimension).unwrap_or(("", Unit::Iota));
    let output_unit = output_unit.unwrap_or(parsed_unit);

    match parse_dim_diagnostic(&dimension) {
        Ok(mut quantity) => {
            quantity = if matches!(
                dimension.trim_start().as_bytes(),
                [b'-', ..] | [0xE2, 0x88, 0x92, ..]
            ) {
                -quantity
            } else {
                quantity
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
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("Failed to parse {dimension:?}: {e:#?}");
            ExitCode::FAILURE
        }
    }
}
