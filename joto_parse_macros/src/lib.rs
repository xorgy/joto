// Copyright 2025 the Joto Authors
// SPDX-License-Identifier: ISC OR Apache-2.0 OR MIT

use joto_parse::u128::parse_dim_diagnostic;
use joto_parse::ParseError;
use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

/// Parse a dimension into an integer literal.
///
/// Example:
///
/// ```
/// use joto_parse_macros::dim;
/// const PITCH: u128 = dim!(21ft 11in);
/// const DEPTH: i64 = dim!(32ft 5 37/64in);
/// const FINE: i16 = dim!(.00001in) + dim!(3nm);
/// const VERY_FINE: i8 = dim!(1 nm);
/// ```
///
/// This should fail at compile time, because it is too small to represent:
///
/// ```compile_fail
/// use joto_parse_macros::dim;
/// const FAIL: i8 = dim!(0.1nm);
/// ```
///
/// If you want to produce a negative quantity, use the negative sign on the outside
/// of the invocation like so:
///
/// ```
/// use joto_parse_macros::dim;
/// const NEGATIVE_NELLY: i128 = -dim!(5ft 3 1/2in);
/// ```
#[proc_macro]
pub fn dim(input: TokenStream) -> TokenStream {
    // We accept bare tokens as well as (some) string literals in `dim!`, so stringify everything.
    let c: Vec<char> = input.to_string().trim().chars().collect();
    // Strip the first set of outer double quotes, as well as literal backslashes inside.
    // If you are escaping characters like fraction slash inside your macro invocation,
    // you might as well just use the const function instead.
    let s = match c.as_slice() {
        ['"', i @ .., '"'] | i => String::from_iter(i.iter().filter(|c| **c != '\\')),
    };
    if s.is_empty() {
        return compile_error("Empty dimension, needs to be something like dim!(21'3 1⁄4\")");
    }

    // Parse with u128 for positive values.
    match parse_dim_diagnostic(&s) {
        Ok(value) => {
            let mut lit = Literal::u128_unsuffixed(value);
            lit.set_span(Span::call_site());
            TokenStream::from(TokenTree::Literal(lit))
        }
        Err(e) => compile_error(format_error(&e, &s)),
    }
}

fn format_error(e: &ParseError, s: &str) -> String {
    use ParseError::*;
    let pre_pre = "Failed to parse dimension (";
    let pos_msg = |at| {
        let pointer = " ".repeat(at + pre_pre.len()) + "^";
        format!("{pre_pre}{s})\n{pointer}\n")
    };
    match e {
        Empty => format!("Failed to parse dimension ({s}) empty string"),
        NoUnit { at } => format!("{}missing or invalid unit", pos_msg(at)),
        EmptyQuantity { at, .. } => format!("{}missing quantity", pos_msg(at)),
        TooBig { unit, at, .. } => format!("{}quantity too large for {:?}", pos_msg(at), unit),
        TooPrecise { unit, at, .. } => {
            format!("{}quantity too precise for {:?}", pos_msg(at), unit)
        }
        BadDenominator { unit, at, .. } => {
            format!("{}invalid denominator for {:?}", pos_msg(at), unit)
        }
        BadNumerator { unit, at, .. } => {
            format!("{}invalid numerator for {:?}", pos_msg(at), unit)
        }
        InvalidCompound {
            inferior,
            found,
            at,
            ..
        } => format!(
            "{}invalid compound unit, found {:?} but expected {:?}",
            pos_msg(at),
            found,
            inferior.superior().unwrap()
        ),
    }
}

fn compile_error(msg: impl AsRef<str>) -> TokenStream {
    let mut ts = TokenStream::new();
    ts.extend(vec![
        TokenTree::Ident(Ident::new("compile_error", Span::call_site())),
        TokenTree::Punct(Punct::new('!', Spacing::Alone)),
        TokenTree::Group({
            let lit = TokenTree::Literal(Literal::string(msg.as_ref()));
            let mut inner = TokenStream::new();
            inner.extend(vec![lit]);
            let mut g = Group::new(Delimiter::Parenthesis, inner);
            g.set_span(Span::call_site());
            g
        }),
    ]);
    ts
}
