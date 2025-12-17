// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Dimension string reformatter using [`joto_parse`] and [`joto_format`], to explore round-trip conversion.

use std::env;
use std::process::ExitCode;

use joto_format::length::{FracType, LengthFormat};
use joto_format::mass::MassFormat;
use joto_format::temperature::TemperatureFormat;
use joto_format::OutputDeviceMode;
use joto_parse::{length as parse_length, mass as parse_mass, temperature as parse_temperature};

const USAGE: &str = "Usage: reformat <dimension...> [--help] [--as <unit>] [--ascii | --complex ] [--prefer-fraction | --prefer-decimal] [--[no-]frac-fallback ] [--[no-]mixed ] [--]";

const HELP: &str = "\
Reformat a dimension string into a specified unit and format.

Usage: reformat <dimension...> [options]

<dimension...>: One or more arguments forming a dimension string (e.g., '1 1/2 in' or '1' '1/2' 'in').
               If your dimension starts with a '-', you may need to use '--' before it (depending on your shell).

Options:
  --as <unit>              Output in the specified unit; supports length, mass, and temperature units.
                           Defaults to the input's unit.
  --ascii                  Output only ASCII characters (e.g., ' for ft, \" for in).
  --complex                Output Unicode characters (e.g., U+2032 for ft, U+2033 for in). Default.
  --prefer-fraction        Prefer whole number fractions (e.g. 37/64) for inches when possible.
  --prefer-decimal         Prefer decimal fractions (e.g., 0.5) for inches.
  --[no-]frac-fallback     Allow decimal fractions as a fallback if whole fractions are inexact. Default on.
  --[no-]mixed             Allow mixed units (e.g., feet and inches) in output. Default mixed units.
  --help, -h               Show this help message.
";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UnitFamily {
    Length,
    Mass,
    Temperature,
}

#[derive(Clone, Copy, Debug)]
enum ParsedUnit {
    Length(parse_length::Unit),
    Mass(parse_mass::Unit),
    Temperature(parse_temperature::Unit),
}

impl ParsedUnit {
    const fn family(self) -> UnitFamily {
        match self {
            ParsedUnit::Length(_) => UnitFamily::Length,
            ParsedUnit::Mass(_) => UnitFamily::Mass,
            ParsedUnit::Temperature(_) => UnitFamily::Temperature,
        }
    }
}

fn is_negative_number_token(s: &str) -> bool {
    let Some(rest) = s.strip_prefix('-') else {
        return false;
    };
    matches!(rest.as_bytes(), [b'0'..=b'9', ..] | [b'.', ..])
}

fn trim_end_like_parser(s: &str) -> &str {
    let mut b = s.as_bytes();
    loop {
        match b {
            // ASCII space.
            [r @ .., b' '] => {
                b = r;
                continue;
            }
            // U+00A0 NO-BREAK SPACE
            [r @ .., 0xC2, 0xA0] => {
                b = r;
                continue;
            }
            // U+FEFF ZERO WIDTH NO-BREAK SPACE
            [r @ .., 0xEF, 0xBB, 0xBF] => {
                b = r;
                continue;
            }
            // U+202F NARROW NO-BREAK SPACE
            [r @ .., 0xE2, 0x80, 0xAF] => {
                b = r;
                continue;
            }
            // U+2009 THIN SPACE
            [r @ .., 0xE2, 0x80, 0x89] => {
                b = r;
                continue;
            }
            // U+2000..=U+200B (various spaces)
            [r @ .., 0xE2, 0x80, 0x80..=0x8B] => {
                b = r;
                continue;
            }
            _ => break,
        }
    }
    // SAFETY: `b` is a suffix-trimmed prefix of `s`, always on a UTF-8 boundary.
    unsafe { core::str::from_utf8_unchecked(b) }
}

fn detect_input_unit(s: &str) -> Option<ParsedUnit> {
    let s = trim_end_like_parser(s);
    if let Some((_, u)) = parse_length::strip_unit(s) {
        return Some(ParsedUnit::Length(u));
    }
    if let Some((_, u)) = parse_mass::strip_unit(s) {
        return Some(ParsedUnit::Mass(u));
    }
    if let Some((_, u)) = parse_temperature::strip_unit(s) {
        return Some(ParsedUnit::Temperature(u));
    }
    None
}

fn parse_as_unit_arg(s: &str) -> Result<ParsedUnit, String> {
    let s = s.trim();
    if s.is_empty() {
        return Err("Empty unit specification for --as".to_owned());
    }
    if let Some((rest, u)) = parse_length::strip_unit(s) {
        if trim_end_like_parser(rest).is_empty() {
            return Ok(ParsedUnit::Length(u));
        }
    }
    if let Some((rest, u)) = parse_mass::strip_unit(s) {
        if trim_end_like_parser(rest).is_empty() {
            return Ok(ParsedUnit::Mass(u));
        }
    }
    if let Some((rest, u)) = parse_temperature::strip_unit(s) {
        if trim_end_like_parser(rest).is_empty() {
            return Ok(ParsedUnit::Temperature(u));
        }
    }
    Err(format!("Invalid unit specification for --as: {s}"))
}

fn eprint_at_marker(input: &str, at: usize) {
    let input = trim_end_like_parser(input);
    let mut at = at.min(input.len());
    while at > 0 && !input.is_char_boundary(at) {
        at -= 1;
    }

    let prefix = &input[..at];
    let col = prefix.chars().count();

    let input_dbg = input.escape_debug().to_string();
    let prefix_dbg_len = prefix.escape_debug().to_string().len();

    eprintln!("input: \"{input_dbg}\"");
    eprintln!(
        "{:width$}^ at byte {at}, col {col}",
        "",
        width = "input: ".len() + 1 + prefix_dbg_len
    );
}

fn print_length_error(input: &str, e: parse_length::ParseError) {
    eprintln!("parse error (length): {e:?}");
    match e {
        parse_length::ParseError::Empty => {
            eprint_at_marker(input, 0);
        }
        parse_length::ParseError::NoUnit { at }
        | parse_length::ParseError::EmptyQuantity { at, .. }
        | parse_length::ParseError::TooBig { at, .. }
        | parse_length::ParseError::TooPrecise { at, .. }
        | parse_length::ParseError::BadDenominator { at, .. }
        | parse_length::ParseError::BadNumerator { at, .. }
        | parse_length::ParseError::InvalidCompound { at, .. } => {
            eprint_at_marker(input, at);
        }
    }
}

fn print_mass_error(input: &str, e: parse_mass::ParseError) {
    eprintln!("parse error (mass): {e:?}");
    match e {
        parse_mass::ParseError::Empty => {
            eprint_at_marker(input, 0);
        }
        parse_mass::ParseError::NoUnit { at }
        | parse_mass::ParseError::EmptyQuantity { at, .. }
        | parse_mass::ParseError::TooBig { at, .. }
        | parse_mass::ParseError::TooPrecise { at, .. }
        | parse_mass::ParseError::InvalidCompound { at, .. } => {
            eprint_at_marker(input, at);
        }
    }
}

fn print_temperature_error(input: &str, e: parse_temperature::ParseError) {
    eprintln!("parse error (temperature): {e:?}");
    match e {
        parse_temperature::ParseError::Empty => {
            eprint_at_marker(input, 0);
        }
        parse_temperature::ParseError::NoUnit { at }
        | parse_temperature::ParseError::EmptyQuantity { at, .. }
        | parse_temperature::ParseError::TooBig { at, .. }
        | parse_temperature::ParseError::TooSmall { at, .. }
        | parse_temperature::ParseError::TooPrecise { at, .. }
        | parse_temperature::ParseError::InvalidSign { at, .. } => {
            eprint_at_marker(input, at);
        }
    }
}

fn main() -> ExitCode {
    let mut args = env::args().skip(1).peekable();
    let Some(_) = args.peek() else {
        eprintln!("{USAGE}");
        return ExitCode::SUCCESS;
    };

    let mut dimension_parts: Vec<String> = Vec::new();
    let mut output_unit: Option<ParsedUnit> = None;

    let mut output_device_mode = OutputDeviceMode::Complex;
    let mut length_format = LengthFormat::default();
    let mut mass_format = MassFormat::default();
    let mut temperature_format = TemperatureFormat::default();
    let mut used_length_only_flag = false;

    while let Some(arg) = args.next() {
        match arg.as_ref() {
            "--help" | "-h" => {
                eprintln!("{HELP}");
                return ExitCode::SUCCESS;
            }
            "--as" => {
                if let Some(unit_str) = args.next() {
                    match parse_as_unit_arg(&unit_str) {
                        Ok(u) => output_unit = Some(u),
                        Err(e) => {
                            eprintln!("{e}");
                            return ExitCode::FAILURE;
                        }
                    }
                } else {
                    eprintln!("Missing unit for --as");
                    return ExitCode::FAILURE;
                }
            }
            "--ascii" | "-a" => {
                output_device_mode = OutputDeviceMode::Ascii;
            }
            "--complex" | "-c" => {
                output_device_mode = OutputDeviceMode::Complex;
            }
            "--prefer-fraction" => {
                length_format.frac_type = FracType::Whole;
                used_length_only_flag = true;
            }
            "--prefer-decimal" => {
                length_format.frac_type = FracType::Decimal;
                used_length_only_flag = true;
            }
            "--no-mixed" => {
                length_format.mixed = false;
                used_length_only_flag = true;
            }
            "--mixed" => {
                length_format.mixed = true;
                used_length_only_flag = true;
            }
            "--no-frac-fallback" => {
                length_format.allow_frac_fallback = false;
                used_length_only_flag = true;
            }
            "--frac-fallback" => {
                length_format.allow_frac_fallback = true;
                used_length_only_flag = true;
            }
            "--" => {
                dimension_parts.extend(args);
                break;
            }
            arg if arg.starts_with("--") => {
                eprintln!("Unknown flag: {arg}");
                eprintln!("{USAGE}");
                return ExitCode::FAILURE;
            }
            arg if arg.starts_with('-') && !is_negative_number_token(arg) => {
                eprintln!("Unknown flag: {arg}");
                eprintln!("{USAGE}");
                return ExitCode::FAILURE;
            }
            arg => {
                dimension_parts.push(arg.to_owned());
            }
        }
    }

    length_format.output_device_mode = output_device_mode;
    mass_format.output_device_mode = output_device_mode;
    temperature_format.output_device_mode = output_device_mode;

    if dimension_parts.is_empty() {
        eprintln!("No dimension provided");
        return ExitCode::FAILURE;
    }

    let dimension = dimension_parts.join(" ");
    let parsed_unit = match detect_input_unit(&dimension) {
        Some(u) => u,
        None => {
            eprintln!("Unable to determine unit family for input (missing/invalid unit suffix).");
            eprintln!("input: {:?}", trim_end_like_parser(&dimension));
            return ExitCode::FAILURE;
        }
    };

    if used_length_only_flag && !matches!(parsed_unit, ParsedUnit::Length(_)) {
        eprintln!(
            "Length-only formatting flags were supplied, but input is {:?}.",
            parsed_unit.family()
        );
        return ExitCode::FAILURE;
    }

    let output_unit = if let Some(out) = output_unit {
        if out.family() != parsed_unit.family() {
            eprintln!(
                "Mismatched unit families: input is {:?}, --as is {:?}.",
                parsed_unit.family(),
                out.family()
            );
            return ExitCode::FAILURE;
        }
        out
    } else {
        parsed_unit
    };

    let eqsign = match output_device_mode {
        OutputDeviceMode::Ascii => "~",
        OutputDeviceMode::Complex => "≈",
    };

    match (parsed_unit, output_unit) {
        (ParsedUnit::Length(_), ParsedUnit::Length(out_u)) => {
            match parse_length::i128::parse_dim_diagnostic(&dimension) {
                Ok(mut quantity) => {
                    // Length parsing intentionally ignores signs; interpret leading signs here.
                    quantity = if matches!(
                        dimension.trim_start().as_bytes(),
                        [b'-', ..] | [0xE2, 0x88, 0x92, ..]
                    ) {
                        -quantity
                    } else {
                        quantity
                    };

                    let formatted =
                        joto_format::length::i128::format_dim(quantity, out_u, length_format);
                    let eqsign = if formatted.exact { "=" } else { eqsign };
                    println!("{eqsign} {}", formatted.as_ref());
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    print_length_error(&dimension, e);
                    ExitCode::FAILURE
                }
            }
        }
        (ParsedUnit::Mass(_), ParsedUnit::Mass(out_u)) => {
            match parse_mass::i128::parse_dim_diagnostic(&dimension) {
                Ok(mut quantity) => {
                    // Mass parsing intentionally ignores signs; interpret leading signs here.
                    quantity = if matches!(
                        dimension.trim_start().as_bytes(),
                        [b'-', ..] | [0xE2, 0x88, 0x92, ..]
                    ) {
                        -quantity
                    } else {
                        quantity
                    };

                    let formatted =
                        joto_format::mass::i128::format_dim(quantity, out_u, mass_format);
                    let eqsign = if formatted.exact { "=" } else { eqsign };
                    println!("{eqsign} {}", formatted.as_ref());
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    print_mass_error(&dimension, e);
                    ExitCode::FAILURE
                }
            }
        }
        (ParsedUnit::Temperature(_), ParsedUnit::Temperature(out_u)) => {
            match parse_temperature::i128::parse_dim_diagnostic(&dimension) {
                Ok(quantity) => {
                    let formatted = joto_format::temperature::i128::format_dim(
                        quantity,
                        out_u,
                        temperature_format,
                    );
                    let eqsign = if formatted.exact { "=" } else { eqsign };
                    println!("{eqsign} {}", formatted.as_ref());
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    print_temperature_error(&dimension, e);
                    ExitCode::FAILURE
                }
            }
        }
        _ => {
            eprintln!("Internal error: unit family mismatch after validation.");
            ExitCode::FAILURE
        }
    }
}
