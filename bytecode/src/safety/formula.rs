// Formula AST, Tokenizer, and Parser for Safety contracts

use std::collections::HashMap;
use crate::value::Value;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Formula {
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),
    Equal(Box<Expr>, Box<Expr>),
    NotEqual(Box<Expr>, Box<Expr>),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Int(i64),
    Float(String),
    Bool(bool),
    In(usize),
    Out(usize),
    InField(usize, usize),
    OutField(usize, usize),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
    Not(Box<Expr>),
    Var(String),
    Call(String, Vec<Expr>),
    Formula(Box<Formula>),
    Field(Box<Expr>, usize),
    Tuple(Vec<Expr>),
    Cond(Box<Expr>, Box<Expr>, Box<Expr>),
    LessThan(Box<Expr>, Box<Expr>),
    LessThanEqual(Box<Expr>, Box<Expr>),
    Equal(Box<Expr>, Box<Expr>),
}

// =============================================================================
// Pretty Printer
// =============================================================================

impl Formula {
    pub fn to_string_pretty(&self) -> String {
        match self {
            Formula::And(a, b) => format!("({} && {})", a.to_string_pretty(), b.to_string_pretty()),
            Formula::Or(a, b) => format!("({} || {})", a.to_string_pretty(), b.to_string_pretty()),
            Formula::Implies(a, b) => format!("({} ==> {})", a.to_string_pretty(), b.to_string_pretty()),
            Formula::Not(a) => format!("(!{})", a.to_string_pretty()),
            Formula::Equal(a, b) => format!("({} == {})", a.to_string_pretty(), b.to_string_pretty()),
            Formula::NotEqual(a, b) => format!("({} != {})", a.to_string_pretty(), b.to_string_pretty()),
            Formula::Expr(e) => e.to_string_pretty(),
        }
    }
}

impl Expr {
    pub fn to_string_pretty(&self) -> String {
        match self {
            Expr::Int(i) => i.to_string(),
            Expr::Float(f) => f.clone(),
            Expr::Bool(b) => b.to_string(),
            Expr::In(idx) => format!("in[{}]", idx),
            Expr::Out(idx) => format!("out[{}]", idx),
            Expr::InField(idx, field) => format!("in[{}].{}", idx, field),
            Expr::OutField(idx, field) => format!("out[{}].{}", idx, field),
            Expr::Add(a, b) => format!("({} + {})", a.to_string_pretty(), b.to_string_pretty()),
            Expr::Sub(a, b) => format!("({} - {})", a.to_string_pretty(), b.to_string_pretty()),
            Expr::Mul(a, b) => format!("({} * {})", a.to_string_pretty(), b.to_string_pretty()),
            Expr::Div(a, b) => format!("({} / {})", a.to_string_pretty(), b.to_string_pretty()),
            Expr::Mod(a, b) => format!("({} % {})", a.to_string_pretty(), b.to_string_pretty()),
            Expr::Neg(a) => format!("(-{})", a.to_string_pretty()),
            Expr::Not(a) => format!("(!{})", a.to_string_pretty()),
            Expr::Var(name) => name.clone(),
            Expr::Call(name, args) => {
                let args_str: Vec<String> = args.iter().map(|a| a.to_string_pretty()).collect();
                format!("{}({})", name, args_str.join(", "))
            }
            Expr::Formula(f) => f.to_string_pretty(),
            Expr::Field(e, field) => format!("{}.{}", e.to_string_pretty(), field),
            Expr::Tuple(elms) => {
                let elms_str: Vec<String> = elms.iter().map(|e| e.to_string_pretty()).collect();
                format!("({})", elms_str.join(", "))
            }
            Expr::Cond(c, t, e) => format!("(if {} then {} else {})", c.to_string_pretty(), t.to_string_pretty(), e.to_string_pretty()),
            Expr::LessThan(a, b) => format!("({} < {})", a.to_string_pretty(), b.to_string_pretty()),
            Expr::LessThanEqual(a, b) => format!("({} <= {})", a.to_string_pretty(), b.to_string_pretty()),
            Expr::Equal(a, b) => format!("({} == {})", a.to_string_pretty(), b.to_string_pretty()),
        }
    }
}

// =============================================================================
// Tokenizer
// =============================================================================

#[derive(Debug, Clone, PartialEq)]
enum FormulaToken {
    And,
    Or,
    Implies,
    Not,
    Eq,
    Neq,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Dot,
    In,
    Out,
    Bool(bool),
    Int(i64),
    Ident(String),
    Comma,
}

fn tokenize_formula(input: &str) -> Result<Vec<FormulaToken>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            c if c.is_whitespace() => {
                chars.next();
            }
            '&' => {
                chars.next();
                if chars.peek() == Some(&'&') {
                    chars.next();
                    tokens.push(FormulaToken::And);
                } else {
                    return Err("Expected &&".to_string());
                }
            }
            '|' => {
                chars.next();
                if chars.peek() == Some(&'|') {
                    chars.next();
                    tokens.push(FormulaToken::Or);
                } else {
                    return Err("Expected ||".to_string());
                }
            }
            '=' => {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    if chars.peek() == Some(&'>') {
                        chars.next();
                        tokens.push(FormulaToken::Implies);
                    } else {
                        tokens.push(FormulaToken::Eq);
                    }
                } else {
                    return Err("Expected == or ==>".to_string());
                }
            }
            '!' => {
                chars.next();
                if chars.peek() == Some(&'=') {
                    chars.next();
                    tokens.push(FormulaToken::Neq);
                } else {
                    tokens.push(FormulaToken::Not);
                }
            }
            '+' => {
                chars.next();
                tokens.push(FormulaToken::Plus);
            }
            '-' => {
                chars.next();
                tokens.push(FormulaToken::Minus);
            }
            '*' => {
                chars.next();
                tokens.push(FormulaToken::Star);
            }
            '/' => {
                chars.next();
                tokens.push(FormulaToken::Slash);
            }
            '%' => {
                chars.next();
                tokens.push(FormulaToken::Percent);
            }
            '(' => {
                chars.next();
                tokens.push(FormulaToken::LParen);
            }
            ')' => {
                chars.next();
                tokens.push(FormulaToken::RParen);
            }
            '[' => {
                chars.next();
                tokens.push(FormulaToken::LBracket);
            }
            ']' => {
                chars.next();
                tokens.push(FormulaToken::RBracket);
            }
            '.' => {
                chars.next();
                tokens.push(FormulaToken::Dot);
            }
            ',' => {
                chars.next();
                tokens.push(FormulaToken::Comma);
            }
            '0'..='9' => {
                let mut num_str = String::new();
                while let Some(&next_c) = chars.peek() {
                    if next_c.is_ascii_digit() {
                        num_str.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                let val = num_str.parse::<i64>().map_err(|e| e.to_string())?;
                tokens.push(FormulaToken::Int(val));
            }
            c if c.is_ascii_alphabetic() || c == '_' || c == ':' => {
                let mut ident = String::new();
                while let Some(&next_c) = chars.peek() {
                    if next_c.is_ascii_alphanumeric() || next_c == '_' || next_c == ':' {
                        ident.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }
                match ident.as_str() {
                    "in" => tokens.push(FormulaToken::In),
                    "out" => tokens.push(FormulaToken::Out),
                    "true" => tokens.push(FormulaToken::Bool(true)),
                    "false" => tokens.push(FormulaToken::Bool(false)),
                    _ => tokens.push(FormulaToken::Ident(ident)),
                }
            }
            other => return Err(format!("Unexpected char in formula: {}", other)),
        }
    }
    Ok(tokens)
}

// =============================================================================
// Parser
// =============================================================================

struct TokenStream<'a> {
    tokens: &'a [FormulaToken],
    pos: usize,
}

impl<'a> TokenStream<'a> {
    fn peek(&self) -> Option<&FormulaToken> {
        self.tokens.get(self.pos)
    }
    fn next(&mut self) -> Option<&FormulaToken> {
        let t = self.tokens.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn expect(&mut self, token: FormulaToken) -> Result<(), String> {
        match self.next() {
            Some(t) if *t == token => Ok(()),
            Some(other) => Err(format!("Expected {:?}, found {:?}", token, other)),
            None => Err(format!("Expected {:?}, found end of input", token)),
        }
    }
}

fn parse_formula(stream: &mut TokenStream) -> Result<Formula, String> {
    parse_conj(stream)
}

fn parse_conj(stream: &mut TokenStream) -> Result<Formula, String> {
    let mut left = parse_disj(stream)?;
    while stream.peek() == Some(&FormulaToken::And) {
        stream.next();
        let right = parse_disj(stream)?;
        left = Formula::And(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn parse_disj(stream: &mut TokenStream) -> Result<Formula, String> {
    let mut left = parse_impl(stream)?;
    while stream.peek() == Some(&FormulaToken::Or) {
        stream.next();
        let right = parse_impl(stream)?;
        left = Formula::Or(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn parse_impl(stream: &mut TokenStream) -> Result<Formula, String> {
    let mut left = parse_comp(stream)?;
    while stream.peek() == Some(&FormulaToken::Implies) {
        stream.next();
        let right = parse_comp(stream)?;
        left = Formula::Implies(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn parse_comp(stream: &mut TokenStream) -> Result<Formula, String> {
    let left = parse_expr(stream)?;
    if let Some(&FormulaToken::Eq) = stream.peek() {
        stream.next();
        let right = parse_expr(stream)?;
        Ok(Formula::Equal(Box::new(left), Box::new(right)))
    } else if let Some(&FormulaToken::Neq) = stream.peek() {
        stream.next();
        let right = parse_expr(stream)?;
        Ok(Formula::NotEqual(Box::new(left), Box::new(right)))
    } else {
        Ok(Formula::Expr(left))
    }
}

fn parse_expr(stream: &mut TokenStream) -> Result<Expr, String> {
    let mut left = parse_term(stream)?;
    while let Some(t) = stream.peek() {
        match t {
            FormulaToken::Plus => {
                stream.next();
                let right = parse_term(stream)?;
                left = Expr::Add(Box::new(left), Box::new(right));
            }
            FormulaToken::Minus => {
                stream.next();
                let right = parse_term(stream)?;
                left = Expr::Sub(Box::new(left), Box::new(right));
            }
            _ => break,
        }
    }
    Ok(left)
}

fn parse_term(stream: &mut TokenStream) -> Result<Expr, String> {
    let mut left = parse_factor(stream)?;
    while let Some(t) = stream.peek() {
        match t {
            FormulaToken::Star => {
                stream.next();
                let right = parse_factor(stream)?;
                left = Expr::Mul(Box::new(left), Box::new(right));
            }
            FormulaToken::Slash => {
                stream.next();
                let right = parse_factor(stream)?;
                left = Expr::Div(Box::new(left), Box::new(right));
            }
            FormulaToken::Percent => {
                stream.next();
                let right = parse_factor(stream)?;
                left = Expr::Mod(Box::new(left), Box::new(right));
            }
            _ => break,
        }
    }
    Ok(left)
}

fn parse_factor(stream: &mut TokenStream) -> Result<Expr, String> {
    let mut base = parse_factor_base(stream)?;
    while stream.peek() == Some(&FormulaToken::Dot) {
        stream.next(); // consume '.'
        let field = match stream.next() {
            Some(FormulaToken::Int(i)) => *i as usize,
            other => return Err(format!("Expected integer field index after '.', found {:?}", other)),
        };
        base = Expr::Field(Box::new(base), field);
    }
    Ok(base)
}

fn parse_factor_base(stream: &mut TokenStream) -> Result<Expr, String> {
    match stream.next().cloned() {
        Some(FormulaToken::Not) => {
            let inner = parse_factor(stream)?;
            Ok(Expr::Not(Box::new(inner)))
        }
        Some(FormulaToken::Minus) => {
            let inner = parse_factor(stream)?;
            Ok(Expr::Neg(Box::new(inner)))
        }
        Some(FormulaToken::In) => {
            stream.expect(FormulaToken::LBracket)?;
            let idx = match stream.next() {
                Some(FormulaToken::Int(i)) => *i as usize,
                other => return Err(format!("Expected integer index, found {:?}", other)),
            };
            stream.expect(FormulaToken::RBracket)?;
            Ok(Expr::In(idx))
        }
        Some(FormulaToken::Out) => {
            stream.expect(FormulaToken::LBracket)?;
            let idx = match stream.next() {
                Some(FormulaToken::Int(i)) => *i as usize,
                other => return Err(format!("Expected integer index, found {:?}", other)),
            };
            stream.expect(FormulaToken::RBracket)?;
            Ok(Expr::Out(idx))
        }
        Some(FormulaToken::Bool(b)) => Ok(Expr::Bool(b)),
        Some(FormulaToken::Int(i)) => Ok(Expr::Int(i)),
        Some(FormulaToken::Ident(name)) => {
            if stream.peek() == Some(&FormulaToken::LParen) {
                stream.next(); // consume '('
                let mut args = Vec::new();
                if stream.peek() != Some(&FormulaToken::RParen) {
                    args.push(parse_expr(stream)?);
                    while stream.peek() == Some(&FormulaToken::Comma) {
                        stream.next();
                        args.push(parse_expr(stream)?);
                    }
                }
                stream.expect(FormulaToken::RParen)?;
                Ok(Expr::Call(name.clone(), args))
            } else {
                Ok(Expr::Var(name.clone()))
            }
        }
        Some(FormulaToken::LParen) => {
            let f = parse_formula(stream)?;
            stream.expect(FormulaToken::RParen)?;
            match f {
                Formula::Expr(e) => Ok(e),
                other => Ok(Expr::Formula(Box::new(other))),
            }
        }
        other => Err(format!("Unexpected factor start: {:?}", other)),
    }
}

pub fn parse_formula_string(input: &str) -> Result<Formula, String> {
    let tokens = tokenize_formula(input)?;
    let mut stream = TokenStream { tokens: &tokens, pos: 0 };
    let formula = parse_formula(&mut stream)?;
    if stream.pos < tokens.len() {
        return Err(format!("Unexpected tokens at end of formula: {:?}", &tokens[stream.pos..]));
    }
    Ok(formula)
}

// =============================================================================
// Substitutions
// =============================================================================

pub fn substitute_formula(f: &Formula, inputs: &[Expr], outputs: &[Expr]) -> Formula {
    match f {
        Formula::And(a, b) => Formula::And(
            Box::new(substitute_formula(a, inputs, outputs)),
            Box::new(substitute_formula(b, inputs, outputs)),
        ),
        Formula::Or(a, b) => Formula::Or(
            Box::new(substitute_formula(a, inputs, outputs)),
            Box::new(substitute_formula(b, inputs, outputs)),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(substitute_formula(a, inputs, outputs)),
            Box::new(substitute_formula(b, inputs, outputs)),
        ),
        Formula::Not(a) => Formula::Not(Box::new(substitute_formula(a, inputs, outputs))),
        Formula::Equal(a, b) => Formula::Equal(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Formula::NotEqual(a, b) => Formula::NotEqual(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Formula::Expr(e) => Formula::Expr(substitute_expr(e, inputs, outputs)),
    }
}

pub fn substitute_expr(e: &Expr, inputs: &[Expr], outputs: &[Expr]) -> Expr {
    match e {
        Expr::In(idx) => inputs[*idx].clone(),
        Expr::Out(idx) => outputs[*idx].clone(),
        Expr::InField(idx, field) => Expr::Field(Box::new(inputs[*idx].clone()), *field),
        Expr::OutField(idx, field) => Expr::Field(Box::new(outputs[*idx].clone()), *field),
        Expr::Field(inner, field) => Expr::Field(Box::new(substitute_expr(inner, inputs, outputs)), *field),
        Expr::Add(a, b) => Expr::Add(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Expr::Div(a, b) => Expr::Div(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Expr::Mod(a, b) => Expr::Mod(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Expr::Neg(a) => Expr::Neg(Box::new(substitute_expr(a, inputs, outputs))),
        Expr::Not(a) => Expr::Not(Box::new(substitute_expr(a, inputs, outputs))),
        Expr::Call(name, args) => {
            let sub_args = args.iter().map(|a| substitute_expr(a, inputs, outputs)).collect();
            Expr::Call(name.clone(), sub_args)
        }
        Expr::Formula(f) => Expr::Formula(Box::new(substitute_formula(f, inputs, outputs))),
        Expr::Tuple(elms) => {
            let sub_elms = elms.iter().map(|elm| substitute_expr(elm, inputs, outputs)).collect();
            Expr::Tuple(sub_elms)
        }
        Expr::Cond(c, t, el) => Expr::Cond(
            Box::new(substitute_expr(c, inputs, outputs)),
            Box::new(substitute_expr(t, inputs, outputs)),
            Box::new(substitute_expr(el, inputs, outputs)),
        ),
        Expr::LessThan(a, b) => Expr::LessThan(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Expr::LessThanEqual(a, b) => Expr::LessThanEqual(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        Expr::Equal(a, b) => Expr::Equal(
            Box::new(substitute_expr(a, inputs, outputs)),
            Box::new(substitute_expr(b, inputs, outputs)),
        ),
        _ => e.clone(),
    }
}

pub fn resolve_symbols_in_formula(f: &Formula, symbols: &HashMap<String, Value>, current_module: &str) -> Formula {
    match f {
        Formula::And(a, b) => Formula::And(
            Box::new(resolve_symbols_in_formula(a, symbols, current_module)),
            Box::new(resolve_symbols_in_formula(b, symbols, current_module)),
        ),
        Formula::Or(a, b) => Formula::Or(
            Box::new(resolve_symbols_in_formula(a, symbols, current_module)),
            Box::new(resolve_symbols_in_formula(b, symbols, current_module)),
        ),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(resolve_symbols_in_formula(a, symbols, current_module)),
            Box::new(resolve_symbols_in_formula(b, symbols, current_module)),
        ),
        Formula::Not(a) => Formula::Not(Box::new(resolve_symbols_in_formula(a, symbols, current_module))),
        Formula::Equal(a, b) => Formula::Equal(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Formula::NotEqual(a, b) => Formula::NotEqual(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Formula::Expr(e) => Formula::Expr(resolve_symbols_in_expr(e, symbols, current_module)),
    }
}

pub fn resolve_symbols_in_expr(e: &Expr, symbols: &HashMap<String, Value>, current_module: &str) -> Expr {
    match e {
        Expr::Var(name) => {
            let mut name_clean = name.clone();
            let mut parts: Vec<&str> = current_module.split("::").filter(|s| !s.is_empty()).collect();
            while name_clean.starts_with("super::") {
                name_clean = name_clean["super::".len()..].to_string();
                if !parts.is_empty() {
                    parts.pop();
                }
            }
            loop {
                let prefix = parts.join("::");
                let fq_name = if prefix.is_empty() {
                    name_clean.clone()
                } else {
                    format!("{}::{}", prefix, name_clean)
                };
                if let Some(Value::Symbol(sym)) = symbols.get(&fq_name) {
                    return Expr::Call("symbol".to_string(), vec![Expr::Int(sym.id as i64)]);
                }
                if parts.is_empty() {
                    break;
                }
                parts.pop();
            }
            e.clone()
        }
        Expr::Field(inner, field) => Expr::Field(Box::new(resolve_symbols_in_expr(inner, symbols, current_module)), *field),
        Expr::Add(a, b) => Expr::Add(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Expr::Div(a, b) => Expr::Div(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Expr::Mod(a, b) => Expr::Mod(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Expr::Neg(a) => Expr::Neg(Box::new(resolve_symbols_in_expr(a, symbols, current_module))),
        Expr::Not(a) => Expr::Not(Box::new(resolve_symbols_in_expr(a, symbols, current_module))),
        Expr::Call(name, args) => {
            let res_args = args.iter().map(|arg| resolve_symbols_in_expr(arg, symbols, current_module)).collect();
            Expr::Call(name.clone(), res_args)
        }
        Expr::Formula(f) => Expr::Formula(Box::new(resolve_symbols_in_formula(f, symbols, current_module))),
        Expr::Tuple(elms) => {
            let res_elms = elms.iter().map(|elm| resolve_symbols_in_expr(elm, symbols, current_module)).collect();
            Expr::Tuple(res_elms)
        }
        Expr::Cond(c, t, el) => Expr::Cond(
            Box::new(resolve_symbols_in_expr(c, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(t, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(el, symbols, current_module)),
        ),
        Expr::LessThan(a, b) => Expr::LessThan(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Expr::LessThanEqual(a, b) => Expr::LessThanEqual(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        Expr::Equal(a, b) => Expr::Equal(
            Box::new(resolve_symbols_in_expr(a, symbols, current_module)),
            Box::new(resolve_symbols_in_expr(b, symbols, current_module)),
        ),
        _ => e.clone(),
    }
}
