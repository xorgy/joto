// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

//! Debug CLI for [`joto_parse`].

use std::env;
use std::error::Error;

use joto_parse::i128::parse_dim;
use joto_parse::{strip_unit, Unit};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args: Vec<String> = env::args().skip(1).collect();

    if args.is_empty() {
        eprintln!("Usage: debugcli [calc] <expression> [--as <unit>]");
        return Ok(());
    }

    let mode = args[0].clone();
    if mode == "calc" {
        args.remove(0);
    }
    let (as_unit, expression_parts) = parse_calc_args(args)?;
    let expression = expression_parts.join(" ");
    let CalcDone {
        sum,
        used_units,
        ops,
    } = calculate(&expression)?;

    if let Some(as_unit) = as_unit {
        let (_, unit) =
            strip_unit(&as_unit).ok_or_else(|| format!("Failed to parse unit {as_unit:?}."))?;
        let unit_mul = unit as i128;

        if unit_mul == 0 {
            return Err("Invalid unit".into());
        }

        if let Some((value, unit)) = exact_repr(sum, unit) {
            println!("= {:>20} {}", value, unit.abbr());
        } else {
            let value = format!("{:.10}", (sum as f64) / (unit_mul as f64));
            println!("≈ {:>20} {}", value, unit.abbr());
        }
    } else if used_units.is_empty() {
        println!("= {sum}");
    } else {
        let mut max_len = 8;
        let mut exact_outputs: Vec<OpTriple> = vec![];
        let mut inexact_outputs: Vec<OpTriple> = vec![];
        for unit in used_units.iter() {
            if let Some((quantity, base_unit)) = exact_repr(sum, *unit) {
                exact_outputs.push(('=', quantity, base_unit));
                if let Some(sup) = unit.superior() {
                    if sum.unsigned_abs() > sup as u128 && !used_units.contains(&sup) {
                        if let Some((quantity, base_unit)) = exact_repr(sum, sup) {
                            exact_outputs.push(('=', quantity, base_unit));
                        }
                    }
                }
            } else {
                let unit_mul = *unit as i128;
                inexact_outputs.push((
                    '≈',
                    format!("{:.10}", (sum as f64) / (unit_mul as f64)),
                    *unit,
                ))
            }
        }
        for (_, quantity, _) in ops
            .iter()
            .chain(exact_outputs.iter())
            .chain(inexact_outputs.iter())
        {
            max_len = max_len.max(quantity.len());
        }
        let do_output = |(op, quantity, unit): OpTriple| {
            print!("{op} ",);
            print!("{quantity:>max_len$}");
            if unit.is_si() {
                println!(" {}", unit.abbr());
            } else {
                println!("{}", unit.abbr());
            }
        };
        ops.into_iter().for_each(do_output);
        println!("{}", "─".repeat(max_len + 2));
        exact_outputs.into_iter().for_each(do_output);
        inexact_outputs.into_iter().for_each(do_output);
    }
    Ok(())
}

type OpTriple = (char, String, Unit);

/// Parse arguments to the calc (default) mode.
fn parse_calc_args(args: Vec<String>) -> Result<(Option<String>, Vec<String>), Box<dyn Error>> {
    let mut as_unit = None;
    let mut expression_parts = vec![];
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--as" {
            i += 1;
            if i >= args.len() {
                return Err("Missing unit for --as".into());
            }
            as_unit = Some(args[i].clone());
            i += 1;
        } else {
            expression_parts.push(args[i].clone());
            i += 1;
        }
    }
    Ok((as_unit, expression_parts))
}

#[derive(Default, Clone, Debug)]
struct CalcDone {
    /// The final value of the calculation.
    sum: i128,
    /// The units used in the calculation, in order of introduction.
    used_units: Vec<Unit>,
    /// The sequence of operations undertaken, and their operands.
    ops: Vec<OpTriple>,
}

/// Run the calculations for the calc mode.
fn calculate(expression: &str) -> Result<CalcDone, Box<dyn Error>> {
    let tokens: Vec<&str> = expression.split_whitespace().collect();
    let mut iter = tokens.iter().peekable();
    let mut c = CalcDone::default();
    let mut op = ' ';
    c.sum = parse_dim("0io").unwrap();

    while let Some(token) = iter.next() {
        if *token == "+" {
            op = '+';
            continue;
        } else if *token == "-" {
            op = '-';
            continue;
        } else {
            let mut term_str = token.to_string();
            while let Some(&&next) = iter.peek() {
                if next == "+" || next == "-" {
                    break;
                }
                term_str.push(' ');
                term_str.push_str(iter.next().unwrap());
            }
            let value = parse_dim(&term_str)
                .ok_or_else(|| format!("Failed to parse dimension {:?}.", &term_str))?;
            let fmt = term_str.trim();
            let (fmt, unit) = strip_unit(fmt).unwrap();
            // Preserve order of introduction.
            if !c.used_units.contains(&unit) {
                c.used_units.push(unit);
            }

            c.ops.push((op, fmt.trim().to_owned(), unit));

            match op {
                ' ' | '+' => {
                    c.sum += value;
                }
                '-' => {
                    c.sum -= value;
                }
                _ => {}
            }
        }
    }

    Ok(c)
}

/// Compute the exact representation of the sum in the given unit, if possible.
fn exact_repr(sum: i128, unit: Unit) -> Option<(String, Unit)> {
    let unit_mul = unit as u128;
    let sign = if sum < 0 { "-" } else { "" };
    let abs_sum = sum.unsigned_abs();
    let abs_int = abs_sum / unit_mul;
    let abs_frac = abs_sum % unit_mul;
    if abs_frac == 0 {
        return Some((format!("{sign}{abs_int}"), unit));
    }

    if unit == Unit::Inch {
        let dens = [2u128, 4, 8, 16, 32, 64];
        for den in dens {
            let sub_unit = unit_mul / den;
            if abs_frac % sub_unit == 0 {
                let num = abs_frac / sub_unit;
                let frac_part = format!("{num}\u{2044}{den}");
                return Some((
                    if abs_int == 0 {
                        format!("{sign}{frac_part}")
                    } else {
                        format!("{sign}{abs_int}\u{202F}{frac_part}")
                    },
                    unit,
                ));
            }
        }
    }

    if let Some(inf) = unit.inferior() {
        if let Some((inf_str, _)) = exact_repr(abs_frac as i128, inf) {
            return Some(if abs_int == 0 {
                (format!("{sign}{inf_str}"), inf)
            } else {
                (format!("{sign}{abs_int}{} {inf_str}", unit.abbr()), inf)
            });
        }
    }

    let lsd = unit.least_significant_digit_value() as u128;
    if lsd == 0 || abs_frac % lsd != 0 {
        return None;
    }
    let abs_frac_digits = abs_frac / lsd;
    let max_d = unit.max_decimal_digits() as usize;
    let frac_str = format!("{abs_frac_digits:0max_d$}")
        .trim_end_matches('0')
        .to_string();
    if frac_str.is_empty() {
        return Some((format!("{sign}{abs_int}"), unit));
    }
    if abs_int == 0 {
        Some((format!("{sign}0.{frac_str}"), unit))
    } else {
        Some((format!("{sign}{abs_int}.{frac_str}"), unit))
    }
}
