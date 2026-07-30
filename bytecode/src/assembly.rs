use std::collections::{HashMap, HashSet};
use crate::library::{Library, SentenceIndex, Annotation};
use crate::opcode::Instruction;
use crate::resolve::{ModuleId, ModuleItem, ModuleTree, ResolvedItem};
use crate::value::{Value, Symbol};

pub use crate::resolve::{Path, PathSegment};

/// Token types for the assembly lexer.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Export,
    SymbolKeyword,
    TestKeyword,
    ModKeyword,
    SentenceKeyword,
    FunctionKeyword,
    TypeKeyword,
    EnumKeyword,
    DoubleColon,
    Semicolon,
    Identifier(String),
    StringLiteral(String),
    LBrace,
    RBrace,
    Hash,
    LBracket,
    RBracket,
    LParen,
    RParen,
    Comma,
    Colon,
    Pipe,
    Int(i64),
    Float(f64),
    Bool(bool),
}

/// Tokenizer split logic.
fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let mut chars = input.chars().peekable();
    let mut line = 1;

    while let Some(&c) = chars.peek() {
        match c {
            '\n' => {
                line += 1;
                chars.next();
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            '/' => {
                chars.next();
                if chars.peek() == Some(&'/') {
                    chars.next();
                    // Comment, consume until end of line
                    while let Some(&next_c) = chars.peek() {
                        if next_c == '\n' {
                            break;
                        }
                        chars.next();
                    }
                } else {
                    return Err(format!("Line {}: Unexpected character '/'", line));
                }
            }
            '{' => {
                tokens.push(Token::LBrace);
                chars.next();
            }
            '}' => {
                tokens.push(Token::RBrace);
                chars.next();
            }
            '#' => {
                tokens.push(Token::Hash);
                chars.next();
            }
            '[' => {
                tokens.push(Token::LBracket);
                chars.next();
            }
            ']' => {
                tokens.push(Token::RBracket);
                chars.next();
            }
            '(' => {
                tokens.push(Token::LParen);
                chars.next();
            }
            ')' => {
                tokens.push(Token::RParen);
                chars.next();
            }
            ',' => {
                tokens.push(Token::Comma);
                chars.next();
            }
            ';' => {
                tokens.push(Token::Semicolon);
                chars.next();
            }
            ':' => {
                chars.next();
                if chars.peek() == Some(&':') {
                    chars.next();
                    tokens.push(Token::DoubleColon);
                } else {
                    tokens.push(Token::Colon);
                }
            }

            '|' => {
                tokens.push(Token::Pipe);
                chars.next();
            }
            '"' => {
                chars.next(); // consume '"'
                let mut string_val = String::new();
                let mut closed = false;
                while let Some(next_c) = chars.next() {
                    if next_c == '"' {
                        closed = true;
                        break;
                    }
                    string_val.push(next_c);
                }
                if !closed {
                    return Err(format!("Line {}: Unclosed string literal", line));
                }
                tokens.push(Token::StringLiteral(string_val));
            }
            // Parse negative or positive numbers
            '-' | '0'..='9' => {
                let mut number_str = String::new();
                if c == '-' {
                    number_str.push(chars.next().unwrap());
                }

                while let Some(&next_c) = chars.peek() {
                    if next_c.is_ascii_digit() {
                        number_str.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                let mut is_float = false;
                if let Some(&'.') = chars.peek() {
                    chars.next(); // consume '.'
                    number_str.push('.');
                    is_float = true;

                    while let Some(&next_c) = chars.peek() {
                        if next_c.is_ascii_digit() {
                            number_str.push(chars.next().unwrap());
                        } else {
                            break;
                        }
                    }
                }

                if is_float {
                    let val = number_str.parse::<f64>()
                        .map_err(|e| format!("Line {}: Invalid float '{}': {}", line, number_str, e))?;
                    tokens.push(Token::Float(val));
                } else {
                    if number_str == "-" {
                        return Err(format!("Line {}: Minus sign without digits", line));
                    }
                    let val = number_str.parse::<i64>()
                        .map_err(|e| format!("Line {}: Invalid integer '{}': {}", line, number_str, e))?;
                    tokens.push(Token::Int(val));
                }
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let mut ident = String::new();
                while let Some(&next_c) = chars.peek() {
                    if next_c.is_ascii_alphanumeric() || next_c == '_' {
                        ident.push(chars.next().unwrap());
                    } else {
                        break;
                    }
                }

                match ident.as_str() {
                    "export" => tokens.push(Token::Export),
                    "symbol" => tokens.push(Token::SymbolKeyword),
                    "test" => tokens.push(Token::TestKeyword),
                    "mod" => tokens.push(Token::ModKeyword),
                    "sentence" => tokens.push(Token::SentenceKeyword),
                    "function" => tokens.push(Token::FunctionKeyword),
                    "type" => tokens.push(Token::TypeKeyword),
                    "enum" => tokens.push(Token::EnumKeyword),
                    "true" => tokens.push(Token::Bool(true)),
                    "false" => tokens.push(Token::Bool(false)),
                    _ => tokens.push(Token::Identifier(ident)),
                }
            }
            other => {
                return Err(format!("Line {}: Unexpected character '{}'", line, other));
            }
        }
    }

    Ok(tokens)
}

struct TokenStream {
    tokens: Vec<Token>,
    position: usize,
}

impl TokenStream {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn peek_at(&self, offset: usize) -> Option<&Token> {
        self.tokens.get(self.position + offset)
    }

    fn next(&mut self) -> Option<Token> {
        if self.position < self.tokens.len() {
            let t = self.tokens[self.position].clone();
            self.position += 1;
            Some(t)
        } else {
            None
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), String> {
        match self.next() {
            Some(t) if t == expected => Ok(()),
            Some(other) => Err(format!("Expected {:?}, found {:?}", expected, other)),
            None => Err(format!("Expected {:?}, found end of input", expected)),
        }
    }
}

/// Parses values into ParsedValue AST nodes.
fn parse_value(stream: &mut TokenStream) -> Result<ParsedValue, String> {
    match stream.next() {
        Some(Token::Bool(b)) => Ok(ParsedValue::Bool(b)),
        Some(Token::Int(i)) => Ok(ParsedValue::Int(i)),
        Some(Token::Float(f)) => Ok(ParsedValue::Float(f)),
        Some(Token::Identifier(name)) => {
            let path = parse_path(stream, name)?;
            Ok(ParsedValue::SymbolRef(path))
        }
        Some(Token::LParen) => {
            let mut elements = Vec::new();
            if stream.peek() == Some(&Token::RParen) {
                stream.next(); // consume ')'
                return Ok(ParsedValue::Tuple(elements));
            }

            loop {
                let val = parse_value(stream)?;
                elements.push(val);

                match stream.peek() {
                    Some(&Token::Comma) => {
                        stream.next(); // consume ','
                        if stream.peek() == Some(&Token::RParen) {
                            stream.next(); // consume trailing comma and ')'
                            break;
                        }
                    }
                    Some(&Token::RParen) => {
                        stream.next(); // consume ')'
                        break;
                    }
                    other => {
                        return Err(format!("Expected ',' or ')', found {:?}", other));
                    }
                }
            }
            Ok(ParsedValue::Tuple(elements))
        }
        Some(other) => Err(format!("Expected value, found {:?}", other)),
        None => Err("Expected value, found end of input".to_string()),
    }
}

fn parse_path(stream: &mut TokenStream, first_ident: String) -> Result<Path, String> {
    let mut segments = vec![parse_segment(&first_ident)];
    while let Some(&Token::DoubleColon) = stream.peek() {
        stream.next(); // consume '::'
        match stream.next() {
            Some(Token::Identifier(name)) => {
                segments.push(parse_segment(&name));
            }
            Some(other) => return Err(format!("Expected identifier after '::', found {:?}", other)),
            None => return Err("Expected identifier after '::', found end of input".to_string()),
        }
    }
    Ok(Path { segments })
}

fn parse_segment(name: &str) -> PathSegment {
    match name {
        "crate" => PathSegment::Crate,
        "super" => PathSegment::Super,
        other => PathSegment::Identifier(other.to_string()),
    }
}

fn parse_type_spec(stream: &mut TokenStream) -> Result<TypeSpec, String> {
    parse_type_disjunction(stream)
}

fn parse_type_disjunction(stream: &mut TokenStream) -> Result<TypeSpec, String> {
    let mut left = parse_type_primary(stream)?;
    while stream.peek() == Some(&Token::Pipe) {
        stream.next(); // consume '|'
        let right = parse_type_primary(stream)?;
        match left {
            TypeSpec::Union(ref mut variants) => {
                variants.push(right);
            }
            _ => {
                left = TypeSpec::Union(vec![left, right]);
            }
        }
    }
    Ok(left)
}

fn parse_type_primary(stream: &mut TokenStream) -> Result<TypeSpec, String> {
    match stream.peek() {
        Some(&Token::LParen) => {
            stream.next(); // consume '('
            let mut elements = Vec::new();
            if stream.peek() != Some(&Token::RParen) {
                loop {
                    elements.push(parse_type_spec(stream)?);
                    match stream.peek() {
                        Some(&Token::Comma) => {
                            stream.next();
                            if stream.peek() == Some(&Token::RParen) {
                                break;
                            }
                        }
                        Some(&Token::RParen) => {
                            break;
                        }
                        other => return Err(format!("Expected ',' or ')', found {:?}", other)),
                    }
                }
            }
            stream.expect(Token::RParen)?;
            Ok(TypeSpec::Tuple(elements))
        }
        Some(&Token::Bool(b)) => {
            stream.next();
            Ok(TypeSpec::Literal(ParsedValue::Bool(b)))
        }
        Some(&Token::Int(i)) => {
            stream.next();
            Ok(TypeSpec::Literal(ParsedValue::Int(i)))
        }
        Some(&Token::Float(f)) => {
            stream.next();
            Ok(TypeSpec::Literal(ParsedValue::Float(f)))
        }
        Some(&Token::SymbolKeyword) => {
            stream.next();
            Ok(TypeSpec::Primitive(PrimitiveType::Symbol))
        }
        Some(Token::Identifier(name)) => {
            let name_cloned = name.clone();
            stream.next(); // consume identifier
            
            // Check if it's a primitive type keyword (lowercase only)
            match name_cloned.as_str() {
                "int" => Ok(TypeSpec::Primitive(PrimitiveType::Int)),
                "bool" => Ok(TypeSpec::Primitive(PrimitiveType::Bool)),
                "float" => Ok(TypeSpec::Primitive(PrimitiveType::Float)),
                "symbol" => Ok(TypeSpec::Primitive(PrimitiveType::Symbol)),
                "tuple" => Ok(TypeSpec::Primitive(PrimitiveType::Tuple)),
                _ => {
                    // Otherwise, parse it as a path (which could be a user-defined type or a symbol reference)
                    let path = parse_path(stream, name_cloned)?;
                    Ok(TypeSpec::Path(path))
                }
            }
        }
        other => Err(format!("Expected type specification, found {:?}", other)),
    }
}

/// Parses a target which is either a named label or an inline `{}` block.
fn parse_target(stream: &mut TokenStream) -> Result<Target, String> {
    match stream.peek() {
        Some(&Token::Identifier(_)) => {
            if let Some(Token::Identifier(name)) = stream.next() {
                let path = parse_path(stream, name)?;
                Ok(Target::Label(path))
            } else {
                unreachable!()
            }
        }
        Some(&Token::LBrace) => {
            let sentence = parse_sentence_body(stream)?;
            Ok(Target::Inline(sentence))
        }
        other => Err(format!("Expected label target or inline block '{{', found {:?}", other)),
    }
}

fn parse_sentence_body(stream: &mut TokenStream) -> Result<ParsedSentence, String> {
    stream.expect(Token::LBrace)?;
    let mut instructions = Vec::new();

    while stream.peek() != Some(&Token::RBrace) && stream.peek().is_some() {
        let inst = parse_instruction(stream)?;
        instructions.push(inst);
    }

    stream.expect(Token::RBrace)?;
    Ok(ParsedSentence { instructions })
}

fn parse_usize(stream: &mut TokenStream) -> Result<usize, String> {
    match stream.next() {
        Some(Token::Int(val)) if val >= 0 => Ok(val as usize),
        Some(other) => Err(format!("Expected non-negative integer, found {:?}", other)),
        None => Err("Expected non-negative integer, found end of input".to_string()),
    }
}

fn parse_instruction(stream: &mut TokenStream) -> Result<ParsedInstruction, String> {
    let token = stream.next().ok_or_else(|| "Expected instruction, found end of input".to_string())?;
    let name = match token {
        Token::Identifier(name) => name,
        Token::ModKeyword => "mod".to_string(),
        other => return Err(format!("Expected instruction mnemonic, found {:?}", other)),
    };

    match name.as_str() {
        "push" => {
            let val = parse_value(stream)?;
            Ok(ParsedInstruction::Push(val))
        }
        "drop" => {
            let depth = parse_usize(stream)?;
            Ok(ParsedInstruction::Drop(depth))
        }
        "pick" => {
            let depth = parse_usize(stream)?;
            Ok(ParsedInstruction::Pick(depth))
        }
        "roll" => {
            let depth = parse_usize(stream)?;
            Ok(ParsedInstruction::Roll(depth))
        }
        "equal" => Ok(ParsedInstruction::Equal),
        "greater" => Ok(ParsedInstruction::Greater),
        "less" => Ok(ParsedInstruction::Less),
        "add" => Ok(ParsedInstruction::Add),
        "subtract" | "sub" => Ok(ParsedInstruction::Subtract),
        "multiply" | "mul" => Ok(ParsedInstruction::Multiply),
        "divide" | "div" => Ok(ParsedInstruction::Divide),
        "modulo" | "mod" => Ok(ParsedInstruction::Modulo),
        "not" => Ok(ParsedInstruction::Not),
        "and" => Ok(ParsedInstruction::And),
        "or" => Ok(ParsedInstruction::Or),
        "negate" | "neg" => Ok(ParsedInstruction::Negate),
        "print" => Ok(ParsedInstruction::Print),
        "jump" => {
            let target = parse_target(stream)?;
            Ok(ParsedInstruction::Jump(target))
        }
        "branch" => {
            let target_true = parse_target(stream)?;
            let target_false = parse_target(stream)?;
            Ok(ParsedInstruction::Branch(target_true, target_false))
        }
        "panic" => Ok(ParsedInstruction::Panic),
        "assert" => Ok(ParsedInstruction::Assert),
        "assert_equal" | "assert_eq" => Ok(ParsedInstruction::AssertEqual),
        "tuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::Tuple(size))
        }
        "untuple" => {
            let size = parse_usize(stream)?;
            Ok(ParsedInstruction::Untuple(size))
        }
        "symbol_len" => Ok(ParsedInstruction::SymbolLen),
        "symbol_char_at" => Ok(ParsedInstruction::SymbolCharAt),
        "is_int" => Ok(ParsedInstruction::IsInt),
        "is_bool" => Ok(ParsedInstruction::IsBool),
        "is_float" => Ok(ParsedInstruction::IsFloat),
        "is_symbol" => Ok(ParsedInstruction::IsSymbol),
        "is_tuple" => Ok(ParsedInstruction::IsTuple),
        "tuple_length" => Ok(ParsedInstruction::TupleLength),
        other => Err(format!("Unknown instruction mnemonic: '{}'", other)),
    }
}

#[derive(Debug, Clone)]
pub enum ModuleExpr {
    Named(Path),
    Composer {
        composer: String,
        args: Vec<ModuleExpr>,
    },
    Value(ParsedValue),
}

#[derive(Debug, Clone)]
pub enum ResolvedArg {
    Path(Path),
    Value(ParsedValue),
}

enum TopLevelItem {
    SymbolDecl {
        name: String,
        debug_desc: Option<String>,
    },
    Sentence(TopLevelSentence),
    Mod {
        name: String,
        items: Vec<TopLevelItem>,
        is_test: bool,
    },
    Compose {
        name: String,
        composer: String,
        args: Vec<ModuleExpr>,
        is_test: bool,
    },
}

struct TopLevelSentence {
    is_exported: bool,
    is_test: bool,
    name: String,
    body: ParsedSentence,
    annotations: Vec<Annotation>,
    is_type_check: bool,
}

fn is_composer_name(name: &str) -> bool {
    name == "compose_concurrent" || name == "compose_hidden" || name == "compose_prefix" || 
    name == "compose_rename_prefix" || name == "compose_static_closure" ||
    name == "compose_done" || name == "compose_emit" || name == "compose_emit_static" ||
    name == "compose_accept" || name == "compose_accept_static"
}

fn parse_module_expr(stream: &mut TokenStream) -> Result<ModuleExpr, String> {
    if let Some(Token::Identifier(ident)) = stream.peek().cloned() {
        if is_composer_name(&ident) {
            stream.next(); // consume composer name
            stream.expect(Token::LParen)?;
            let mut args = Vec::new();
            if stream.peek() != Some(&Token::RParen) {
                loop {
                    args.push(parse_module_expr(stream)?);
                    if stream.peek() == Some(&Token::Comma) {
                        stream.next();
                    } else {
                        break;
                    }
                }
            }
            stream.expect(Token::RParen)?;
            return Ok(ModuleExpr::Composer { composer: ident, args });
        }
    }

    match stream.peek() {
        Some(Token::Identifier(_)) => {
            let first_ident = match stream.next() {
                Some(Token::Identifier(id)) => id,
                _ => unreachable!(),
            };
            let path = parse_path(stream, first_ident)?;
            Ok(ModuleExpr::Named(path))
        }
        Some(_) => {
            let val = parse_value(stream)?;
            Ok(ModuleExpr::Value(val))
        }
        None => Err("Expected module expression or value, found end of input".to_string()),
    }
}

fn parse_top_level(stream: &mut TokenStream, base_dir: Option<&std::path::Path>) -> Result<Vec<TopLevelItem>, String> {
    parse_items(stream, None, base_dir)
}

fn parse_items(stream: &mut TokenStream, end_token: Option<Token>, base_dir: Option<&std::path::Path>) -> Result<Vec<TopLevelItem>, String> {
    let mut items = Vec::new();

    while stream.peek().is_some() {
        if let Some(ref end) = end_token {
            if stream.peek() == Some(end) {
                break;
            }
        }

        let mut annotations = Vec::new();
        while stream.peek() == Some(&Token::Hash) {
            stream.next(); // consume '#'
            stream.expect(Token::LBracket)?;
            let name = match stream.next() {
                Some(Token::Identifier(name)) => name,
                Some(other) => return Err(format!("Expected annotation name, found {:?}", other)),
                None => return Err("Expected annotation name, found end of input".to_string()),
            };

            let ann = match name.as_str() {
                "arity" => {
                    stream.expect(Token::LParen)?;
                    let n = match stream.next() {
                        Some(Token::Int(val)) => val,
                        Some(other) => return Err(format!("Expected integer for arity first argument, found {:?}", other)),
                        None => return Err("Expected integer for arity first argument, found end of input".to_string()),
                    };
                    stream.expect(Token::Comma)?;
                    let m = match stream.next() {
                        Some(Token::Int(val)) => val,
                        Some(other) => return Err(format!("Expected integer for arity second argument, found {:?}", other)),
                        None => return Err("Expected integer for arity second argument, found end of input".to_string()),
                    };
                    stream.expect(Token::RParen)?;
                    Annotation::Arity(n, m)
                }
                "precondition" => {
                    stream.expect(Token::LParen)?;
                    let first_ident = match stream.next() {
                        Some(Token::Identifier(s)) => s,
                        Some(other) => return Err(format!("Expected identifier for precondition function, found {:?}", other)),
                        None => return Err("Expected identifier for precondition function, found end of input".to_string()),
                    };
                    let path = parse_path(stream, first_ident)?;
                    let mut path_str = String::new();
                    for (i, seg) in path.segments.iter().enumerate() {
                        if i > 0 {
                            path_str.push_str("::");
                        }
                        match seg {
                            PathSegment::Crate => path_str.push_str("crate"),
                            PathSegment::Super => path_str.push_str("super"),
                            PathSegment::Identifier(name) => path_str.push_str(name),
                        }
                    }
                    stream.expect(Token::RParen)?;
                    Annotation::Precondition(path_str)
                }
                "postcondition" => {
                    stream.expect(Token::LParen)?;
                    let first_ident = match stream.next() {
                        Some(Token::Identifier(s)) => s,
                        Some(other) => return Err(format!("Expected identifier for postcondition function, found {:?}", other)),
                        None => return Err("Expected identifier for postcondition function, found end of input".to_string()),
                    };
                    let path = parse_path(stream, first_ident)?;
                    let mut path_str = String::new();
                    for (i, seg) in path.segments.iter().enumerate() {
                        if i > 0 {
                            path_str.push_str("::");
                        }
                        match seg {
                            PathSegment::Crate => path_str.push_str("crate"),
                            PathSegment::Super => path_str.push_str("super"),
                            PathSegment::Identifier(name) => path_str.push_str(name),
                        }
                    }
                    stream.expect(Token::RParen)?;
                    Annotation::Postcondition(path_str)
                }
                "recursive" => {
                    Annotation::Recursive
                }
                "total" => {
                    Annotation::Total
                }
                other => return Err(format!("Unsupported annotation '{}'", other)),
            };
            stream.expect(Token::RBracket)?;
            annotations.push(ann);
        }

        if !annotations.is_empty() {
            let mut is_exported = false;
            let mut is_test = false;

            loop {
                if stream.peek() == Some(&Token::Export) {
                    stream.next();
                    is_exported = true;
                } else if stream.peek() == Some(&Token::TestKeyword) {
                    if stream.peek_at(1) == Some(&Token::ModKeyword) {
                        return Err("Annotations are not supported on modules".to_string());
                    }
                    stream.next();
                    is_test = true;
                } else {
                    break;
                }
            }

            if stream.peek() == Some(&Token::TypeKeyword) {
                stream.next(); // consume 'type'
                let name = match stream.next() {
                    Some(Token::Identifier(name)) => name,
                    Some(other) => return Err(format!("Expected type name identifier, found {:?}", other)),
                    None => return Err("Expected type name identifier, found end of input".to_string()),
                };
                let spec = parse_type_spec(stream)?;
                stream.expect(Token::Semicolon)?;

                let check_sentence = compile_type_to_sentence("check".to_string(), spec, true, annotations)?;
                items.push(TopLevelItem::Mod {
                    name,
                    items: vec![TopLevelItem::Sentence(check_sentence)],
                    is_test: false,
                });
                continue;
            }

            if stream.peek() == Some(&Token::EnumKeyword) {
                let enum_item = parse_enum_decl(stream, annotations)?;
                items.push(enum_item);
                continue;
            }

            let is_function = if stream.peek() == Some(&Token::SentenceKeyword) {
                stream.next();
                false
            } else if stream.peek() == Some(&Token::FunctionKeyword) {
                stream.next();
                true
            } else {
                return Err(format!("Expected 'sentence', 'function', or 'type', found {:?}", stream.peek()));
            };

            let name = match stream.next() {
                Some(Token::Identifier(name)) => name,
                Some(other) => return Err(format!("Expected sentence name identifier, found {:?}", other)),
                None => return Err("Expected sentence name identifier, found end of input".to_string()),
            };

            if stream.peek() == Some(&Token::Colon) {
                stream.next();
            }

            let body = parse_sentence_body(stream)?;

            let mut annotations = annotations;
            if is_function {
                annotations.push(Annotation::Arity(1, 1));
            }

            items.push(TopLevelItem::Sentence(TopLevelSentence {
                is_exported,
                is_test,
                name,
                body,
                annotations,
                is_type_check: false,
            }));
            continue;
        }

        if stream.peek() == Some(&Token::SymbolKeyword) {
            stream.next(); // consume 'symbol'
            let name = match stream.next() {
                Some(Token::Identifier(name)) => name,
                Some(other) => return Err(format!("Expected symbol name identifier, found {:?}", other)),
                None => return Err("Expected symbol name identifier, found end of input".to_string()),
            };

            let debug_desc = if let Some(Token::StringLiteral(_)) = stream.peek() {
                if let Some(Token::StringLiteral(desc)) = stream.next() {
                    Some(desc)
                } else {
                    None
                }
            } else {
                None
            };

            items.push(TopLevelItem::SymbolDecl { name, debug_desc });
        } else {
            let is_test_mod = stream.peek() == Some(&Token::TestKeyword) && stream.peek_at(1) == Some(&Token::ModKeyword);

            if is_test_mod || stream.peek() == Some(&Token::ModKeyword) {
                if is_test_mod {
                    stream.next(); // consume 'test'
                }
                stream.next(); // consume 'mod'
                let name = match stream.next() {
                    Some(Token::Identifier(name)) => name,
                    Some(other) => return Err(format!("Expected module name identifier, found {:?}", other)),
                    None => return Err("Expected module name identifier, found end of input".to_string()),
                };
                
                if let Some(&Token::Identifier(ref ident)) = stream.peek() {
                    if is_composer_name(ident) {
                        let composer = match stream.next() {
                            Some(Token::Identifier(id)) => id,
                            _ => unreachable!(),
                        };
                        stream.expect(Token::LParen)?;
                        let mut args = Vec::new();
                        if stream.peek() != Some(&Token::RParen) {
                            loop {
                                args.push(parse_module_expr(stream)?);
                                if stream.peek() == Some(&Token::Comma) {
                                    stream.next();
                                } else {
                                    break;
                                }
                            }
                        }
                        stream.expect(Token::RParen)?;
                        stream.expect(Token::Semicolon)?;
                        items.push(TopLevelItem::Compose { name, composer, args, is_test: is_test_mod });
                        continue;
                    }
                }
                
                if stream.peek() == Some(&Token::Semicolon) {
                    stream.next(); // consume ';'
                    let base = base_dir.ok_or_else(|| {
                        format!("Cannot load external module '{}' because no base directory context was provided", name)
                    })?;
                    let file_name = format!("{}.hana", name);
                    let file_path = base.join(&file_name);
                    let file_content = std::fs::read_to_string(&file_path)
                        .map_err(|e| format!("Failed to read module file '{}' at {:?}: {}", file_name, file_path, e))?;
                    
                    let tokens = tokenize(&file_content)?;
                    let mut sub_stream = TokenStream { tokens, position: 0 };
                    let new_base = base.join(&name);
                    let mod_items = parse_items(&mut sub_stream, None, Some(&new_base))?;
                    items.push(TopLevelItem::Mod { name, items: mod_items, is_test: is_test_mod });
                } else {
                    stream.expect(Token::LBrace)?;
                    let new_base = base_dir.map(|b| b.join(&name));
                    let mod_items = parse_items(stream, Some(Token::RBrace), new_base.as_deref())?;
                    stream.expect(Token::RBrace)?;
                    items.push(TopLevelItem::Mod { name, items: mod_items, is_test: is_test_mod });
                }
            } else {
            let mut is_exported = false;
            let mut is_test = false;

            loop {
                if stream.peek() == Some(&Token::Export) {
                    stream.next();
                    is_exported = true;
                } else if stream.peek() == Some(&Token::TestKeyword) {
                    stream.next();
                    is_test = true;
                } else {
                    break;
                }
            }

            if stream.peek() == Some(&Token::TypeKeyword) {
                stream.next(); // consume 'type'
                let name = match stream.next() {
                    Some(Token::Identifier(name)) => name,
                    Some(other) => return Err(format!("Expected type name identifier, found {:?}", other)),
                    None => return Err("Expected type name identifier, found end of input".to_string()),
                };
                let spec = parse_type_spec(stream)?;
                stream.expect(Token::Semicolon)?;

                let check_sentence = compile_type_to_sentence("check".to_string(), spec, true, Vec::new())?;
                items.push(TopLevelItem::Mod {
                    name,
                    items: vec![TopLevelItem::Sentence(check_sentence)],
                    is_test: false,
                });
                continue;
            }

            if stream.peek() == Some(&Token::EnumKeyword) {
                let enum_item = parse_enum_decl(stream, Vec::new())?;
                items.push(enum_item);
                continue;
            }

            let is_function = if stream.peek() == Some(&Token::SentenceKeyword) {
                stream.next();
                false
            } else if stream.peek() == Some(&Token::FunctionKeyword) {
                stream.next();
                true
            } else {
                return Err(format!("Expected 'sentence', 'function', or 'type', found {:?}", stream.peek()));
            };

            let name = match stream.next() {
                Some(Token::Identifier(name)) => name,
                Some(other) => return Err(format!("Expected sentence name identifier, found {:?}", other)),
                None => return Err("Expected sentence name identifier, found end of input".to_string()),
            };

            if stream.peek() == Some(&Token::Colon) {
                stream.next();
            }

            let body = parse_sentence_body(stream)?;

            let annotations = if is_function {
                vec![Annotation::Arity(1, 1)]
            } else {
                Vec::new()
            };

            items.push(TopLevelItem::Sentence(TopLevelSentence {
                is_exported,
                is_test,
                name,
                body,
                annotations,
                is_type_check: false,
            }));
        }
        }
    }

    Ok(items)
}

fn parse_enum_decl(
    stream: &mut TokenStream,
    annotations: Vec<Annotation>,
) -> Result<TopLevelItem, String> {
    stream.expect(Token::EnumKeyword)?;
    let enum_name = match stream.next() {
        Some(Token::Identifier(name)) => name,
        Some(other) => return Err(format!("Expected enum name identifier, found {:?}", other)),
        None => return Err("Expected enum name identifier, found end of input".to_string()),
    };

    stream.expect(Token::LBrace)?;

    let mut mod_items = Vec::new();
    let mut variant_paths = Vec::new();

    while stream.peek() != Some(&Token::RBrace) {
        let variant_name = match stream.next() {
            Some(Token::Identifier(v)) => v,
            Some(other) => return Err(format!("Expected variant name identifier, found {:?}", other)),
            None => return Err("Expected variant name identifier, found end of input".to_string()),
        };

        // Require parameter list (e.g., Case1(int, bool) or Case3())
        stream.expect(Token::LParen)?;
        let mut elements = Vec::new();
        if stream.peek() != Some(&Token::RParen) {
            loop {
                elements.push(parse_type_spec(stream)?);
                match stream.peek() {
                    Some(&Token::Comma) => {
                        stream.next();
                        if stream.peek() == Some(&Token::RParen) {
                            break;
                        }
                    }
                    Some(&Token::RParen) => {
                        break;
                    }
                    other => return Err(format!("Expected ',' or ')', found {:?}", other)),
                }
            }
        }
        stream.expect(Token::RParen)?;

        let payload_spec = TypeSpec::Tuple(elements);

        // 1. Symbol declaration: tag
        let tag_decl = TopLevelItem::SymbolDecl {
            name: "tag".to_string(),
            debug_desc: None,
        };

        // 2. Type module: Body
        let body_check_sentence = compile_type_to_sentence("check".to_string(), payload_spec, true, Vec::new())?;
        let body_decl = TopLevelItem::Mod {
            name: "Body".to_string(),
            items: vec![TopLevelItem::Sentence(body_check_sentence)],
            is_test: false,
        };

        // 3. Variant check: type check (tag, Body);
        let variant_spec = TypeSpec::Tuple(vec![
            TypeSpec::Path(Path { segments: vec![
                PathSegment::Identifier(variant_name.clone()),
                PathSegment::Identifier("tag".to_string()),
            ] }),
            TypeSpec::Path(Path { segments: vec![
                PathSegment::Identifier(variant_name.clone()),
                PathSegment::Identifier("Body".to_string()),
            ] }),
        ]);
        let variant_check_sentence = compile_type_to_sentence("check".to_string(), variant_spec, true, Vec::new())?;

        // Wrap them into a submodule variant_name
        let variant_mod = TopLevelItem::Mod {
            name: variant_name.clone(),
            items: vec![
                tag_decl,
                body_decl,
                TopLevelItem::Sentence(variant_check_sentence),
            ],
            is_test: false,
        };
        mod_items.push(variant_mod);

        // Overall check path relative to grandparent (i.e. MyEnum::Case1)
        let variant_path = Path {
            segments: vec![
                PathSegment::Identifier(enum_name.clone()),
                PathSegment::Identifier(variant_name.clone()),
            ],
        };
        variant_paths.push(TypeSpec::Path(variant_path));

        // Variants can be optionally followed by comma
        if stream.peek() == Some(&Token::Comma) {
            stream.next();
        }
    }
    stream.expect(Token::RBrace)?;

    // Overall check: type check MyEnum::Case1 | MyEnum::Case2 | MyEnum::Case3;
    let overall_spec = TypeSpec::Union(variant_paths);
    let overall_check_sentence = compile_type_to_sentence("check".to_string(), overall_spec, true, annotations)?;
    mod_items.push(TopLevelItem::Sentence(overall_check_sentence));

    Ok(TopLevelItem::Mod {
        name: enum_name,
        items: mod_items,
        is_test: false,
    })
}

fn compile_type_to_sentence(
    name: String,
    spec: TypeSpec,
    is_exported: bool,
    mut annotations: Vec<Annotation>,
) -> Result<TopLevelSentence, String> {
    if !annotations.iter().any(|ann| matches!(ann, Annotation::Total)) {
        annotations.push(Annotation::Total);
    }

    let instructions = compile_type_spec(&spec)?;

    Ok(TopLevelSentence {
        is_exported,
        is_test: false,
        name,
        body: ParsedSentence { instructions },
        annotations,
        is_type_check: true,
    })
}

fn compile_type_spec(spec: &TypeSpec) -> Result<Vec<ParsedInstruction>, String> {
    match spec {
        TypeSpec::Primitive(prim) => {
            match prim {
                PrimitiveType::Int => Ok(vec![ParsedInstruction::IsInt]),
                PrimitiveType::Bool => Ok(vec![ParsedInstruction::IsBool]),
                PrimitiveType::Float => Ok(vec![ParsedInstruction::IsFloat]),
                PrimitiveType::Symbol => Ok(vec![ParsedInstruction::IsSymbol]),
                PrimitiveType::Tuple => Ok(vec![ParsedInstruction::IsTuple]),
            }
        }
        TypeSpec::Literal(val) => {
            Ok(vec![
                ParsedInstruction::Push(val.clone()),
                ParsedInstruction::Equal,
            ])
        }
        TypeSpec::Path(path) => {
            Ok(vec![ParsedInstruction::TypeCheckPath(path.clone())])
        }
        TypeSpec::Union(variants) => {
            compile_union(variants)
        }
        TypeSpec::Tuple(elements) => {
            let n = elements.len();
            let else_len_mismatches = ParsedSentence {
                instructions: vec![
                    ParsedInstruction::Drop(0),
                    ParsedInstruction::Push(ParsedValue::Bool(false)),
                ],
            };
            let then_len_matches = if n == 0 {
                ParsedSentence {
                    instructions: vec![
                        ParsedInstruction::Drop(0),
                        ParsedInstruction::Push(ParsedValue::Bool(true)),
                    ],
                }
            } else {
                let mut insts = vec![ParsedInstruction::Untuple(n)];
                
                let first_check = compile_type_spec(&elements[0])?;
                insts.extend(first_check);
                
                for elem in elements.iter().skip(1) {
                    insts.push(ParsedInstruction::Roll(1));
                    let elem_check = compile_type_spec(elem)?;
                    insts.extend(elem_check);
                    insts.push(ParsedInstruction::And);
                }
                
                ParsedSentence { instructions: insts }
            };
            
            let then_is_tuple = ParsedSentence {
                instructions: vec![
                    ParsedInstruction::Pick(0),
                    ParsedInstruction::TupleLength,
                    ParsedInstruction::Push(ParsedValue::Int(n as i64)),
                    ParsedInstruction::Equal,
                    ParsedInstruction::Branch(
                        Target::Inline(then_len_matches),
                        Target::Inline(else_len_mismatches),
                    ),
                ],
            };
            
            let else_not_tuple = ParsedSentence {
                instructions: vec![
                    ParsedInstruction::Drop(0),
                    ParsedInstruction::Push(ParsedValue::Bool(false)),
                ],
            };
            
            Ok(vec![
                ParsedInstruction::Pick(0),
                ParsedInstruction::IsTuple,
                ParsedInstruction::Branch(
                    Target::Inline(then_is_tuple),
                    Target::Inline(else_not_tuple),
                ),
            ])
        }
    }
}

fn compile_union(variants: &[TypeSpec]) -> Result<Vec<ParsedInstruction>, String> {
    if variants.is_empty() {
        return Ok(vec![
            ParsedInstruction::Drop(0),
            ParsedInstruction::Push(ParsedValue::Bool(false)),
        ]);
    }
    if variants.len() == 1 {
        return compile_type_spec(&variants[0]);
    }
    
    let first = &variants[0];
    let rest = &variants[1..];
    
    let then_true = ParsedSentence {
        instructions: vec![
            ParsedInstruction::Drop(0),
            ParsedInstruction::Push(ParsedValue::Bool(true)),
        ],
    };
    
    let else_false = ParsedSentence {
        instructions: compile_union(rest)?,
    };
    
    let mut insts = vec![ParsedInstruction::Pick(0)];
    insts.extend(compile_type_spec(first)?);
    insts.push(ParsedInstruction::Branch(
        Target::Inline(then_true),
        Target::Inline(else_false),
    ));
    
    Ok(insts)
}

#[derive(Debug, Clone)]
pub enum ParsedValue {
    Bool(bool),
    Int(i64),
    Float(f64),
    Tuple(Vec<ParsedValue>),
    SymbolRef(Path),
}

#[derive(Debug, Clone)]
struct ParsedSentence {
    instructions: Vec<ParsedInstruction>,
}

#[derive(Debug, Clone)]
enum Target {
    Label(Path),
    Inline(ParsedSentence),
}

#[derive(Debug, Clone)]
enum ParsedInstruction {
    Push(ParsedValue),
    Drop(usize),
    Pick(usize),
    Roll(usize),
    Equal,
    Greater,
    Less,
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Not,
    Negate,
    Print,
    Jump(Target),
    Branch(Target, Target),
    Panic,
    Assert,
    AssertEqual,
    Tuple(usize),
    Untuple(usize),
    And,
    Or,
    SymbolLen,
    SymbolCharAt,
    IsInt,
    IsBool,
    IsFloat,
    IsSymbol,
    IsTuple,
    TupleLength,
    TypeCheckPath(Path),
}

#[derive(Debug, Clone)]
pub enum TypeSpec {
    Primitive(PrimitiveType),
    Literal(ParsedValue),
    Path(Path),
    Tuple(Vec<TypeSpec>),
    Union(Vec<TypeSpec>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    Int,
    Bool,
    Float,
    Symbol,
    Tuple,
}



/// Everything the tree-building pass accumulates alongside the module tree
/// itself: the flat sentence list to compile, and the library's lookup maps.
struct TreeBuilder {
    tree: ModuleTree,
    symbol_counter: usize,
    sentence_counter: usize,
    /// Each sentence paired with the module its paths resolve against.
    flat_sentences: Vec<(ModuleId, TopLevelSentence)>,
    exports: HashMap<String, SentenceIndex>,
    tests: HashMap<String, SentenceIndex>,
    test_machines: HashSet<String>,
    anon_counter: usize,
}

/// Sentences a test machine module exposes to the runtime.
const MACHINE_SENTENCES: [&str; 7] = [
    "init",
    "accept",
    "emit",
    "process",
    "tau_reduce",
    "is_done",
    "is_ready_to_finish",
];

impl TreeBuilder {
    fn new() -> Self {
        Self {
            tree: ModuleTree::new(),
            symbol_counter: 0,
            sentence_counter: 0,
            flat_sentences: Vec::new(),
            exports: HashMap::new(),
            tests: HashMap::new(),
            test_machines: HashSet::new(),
            anon_counter: 0,
        }
    }

    fn build(&mut self, items: Vec<TopLevelItem>, scope: ModuleId) -> Result<(), String> {
        for item in items {
            match item {
                TopLevelItem::SymbolDecl { name, debug_desc } => {
                    let desc = debug_desc.unwrap_or_else(|| self.tree.fq_name(scope, &name));
                    let symbol = Value::Symbol(Symbol {
                        id: self.symbol_counter,
                        name: desc,
                    });
                    self.symbol_counter += 1;

                    self.tree.declare(scope, name, ModuleItem::Symbol(symbol))?;
                }
                TopLevelItem::Sentence(s) => {
                    let s_idx = SentenceIndex::from(self.sentence_counter);
                    self.sentence_counter += 1;

                    self.tree
                        .declare(scope, s.name.clone(), ModuleItem::Sentence(s_idx))?;

                    let fq_name = self.tree.fq_name(scope, &s.name);
                    if s.is_exported {
                        self.exports.insert(fq_name.clone(), s_idx);
                    }
                    if s.is_test {
                        self.tests.insert(fq_name, s_idx);
                    }

                    self.flat_sentences.push((scope, s));
                }
                TopLevelItem::Mod { name, items: mod_items, is_test } => {
                    let sub_id = self.tree.declare_module(scope, name)?;
                    self.build(mod_items, sub_id)?;
                    if is_test {
                        self.register_test_machine(sub_id, false)?;
                    }
                }
                TopLevelItem::Compose { name, composer, args, is_test } => {
                    let sub_id = self.tree.declare_module(scope, name)?;

                    // Argument expressions are relative to the enclosing module,
                    // not to the module being composed.
                    let mut resolved_args = Vec::new();
                    for arg in &args {
                        resolved_args.push(self.resolve_module_expr(arg, scope)?);
                    }
                    let generated_items = generate_composition_items(&composer, &resolved_args)?;

                    self.build(generated_items, sub_id)?;
                    if is_test {
                        self.register_test_machine(sub_id, true)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Registers a `test mod` as a machine the runtime can drive. Composed
    /// machines additionally export their machine sentences, since the generated
    /// bodies have no `export` markers of their own.
    fn register_test_machine(
        &mut self,
        module: ModuleId,
        export_machine_sentences: bool,
    ) -> Result<(), String> {
        let fq_path = self.tree.path_of(module).join("::");
        if self.tree.sentence(module, "init").is_none() {
            return Err(format!("Test mod '{}' must export an 'init' sentence", fq_path));
        }
        self.test_machines.insert(fq_path);

        if export_machine_sentences {
            for name in MACHINE_SENTENCES {
                if let Some(s_idx) = self.tree.sentence(module, name) {
                    self.exports.insert(self.tree.fq_name(module, name), s_idx);
                }
            }
        }
        Ok(())
    }

    /// Reduces a module expression to something a composer template can name.
    /// Nested composers are materialized as anonymous submodules of `scope`.
    fn resolve_module_expr(
        &mut self,
        expr: &ModuleExpr,
        scope: ModuleId,
    ) -> Result<ResolvedArg, String> {
        match expr {
            ModuleExpr::Named(path) => Ok(ResolvedArg::Path(path.clone())),
            ModuleExpr::Value(val) => Ok(ResolvedArg::Value(val.clone())),
            ModuleExpr::Composer { composer, args } => {
                let mut resolved_args = Vec::new();
                for arg in args {
                    resolved_args.push(self.resolve_module_expr(arg, scope)?);
                }
                let generated_items = generate_composition_items(composer, &resolved_args)?;

                // The name has to be a legal identifier: composer templates are
                // rendered as text and re-tokenized, so it round-trips through
                // the lexer.
                let anon_name = format!("__anon_mod_{}", self.anon_counter);
                self.anon_counter += 1;

                let anon_id = self.tree.declare_module(scope, anon_name.clone())?;
                self.build(generated_items, anon_id)?;

                Ok(ResolvedArg::Path(Path {
                    segments: vec![PathSegment::Identifier(anon_name)],
                }))
            }
        }
    }
}

fn adjust_path(path: &Path) -> Path {
    let mut segments = Vec::new();
    if let Some(first) = path.segments.first() {
        match first {
            PathSegment::Crate => segments = path.segments.clone(),
            _ => {
                segments.push(PathSegment::Super);
                segments.extend(path.segments.clone());
            }
        }
    }
    Path { segments }
}

impl std::fmt::Display for ParsedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParsedValue::Bool(b) => write!(f, "{}", b),
            ParsedValue::Int(i) => write!(f, "{}", i),
            ParsedValue::Float(fl) => write!(f, "{}", fl),
            ParsedValue::Tuple(elements) => {
                write!(f, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                if elements.len() == 1 {
                    write!(f, ",")?;
                }
                write!(f, ")")
            }
            ParsedValue::SymbolRef(path) => write!(f, "{}", path),
        }
    }
}

impl std::fmt::Display for ResolvedArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResolvedArg::Path(p) => write!(f, "{}", p),
            ResolvedArg::Value(v) => write!(f, "{}", v),
        }
    }
}

fn compile_template(template_str: &str, vars: &[(&str, &dyn std::fmt::Display)]) -> Result<Vec<TopLevelItem>, String> {
    let mut rendered = template_str.to_string();
    for (name, val) in vars {
        rendered = rendered.replace(&format!("{{{{{}}}}}", name), &val.to_string());
    }
    let tokens = tokenize(&rendered)?;
    let mut stream = TokenStream { tokens, position: 0 };
    parse_top_level(&mut stream, None)
}

fn extract_paths(args: &[ResolvedArg], composer_name: &str) -> Result<Vec<Path>, String> {
    let mut paths = Vec::new();
    for arg in args {
        match arg {
            ResolvedArg::Path(p) => paths.push(p.clone()),
            ResolvedArg::Value(_) => {
                return Err(format!(
                    "{} expects path arguments, found a literal value",
                    composer_name
                ));
            }
        }
    }
    Ok(paths)
}

const TEMPLATE_CONCURRENT: &str = include_str!("templates/compose_concurrent.tmpl.hana");
const TEMPLATE_HIDDEN: &str = include_str!("templates/compose_hidden.tmpl.hana");
const TEMPLATE_PREFIX: &str = include_str!("templates/compose_prefix.tmpl.hana");
const TEMPLATE_RENAME_PREFIX: &str = include_str!("templates/compose_rename_prefix.tmpl.hana");
const TEMPLATE_STATIC_CLOSURE: &str = include_str!("templates/compose_static_closure.tmpl.hana");
const TEMPLATE_DONE: &str = include_str!("templates/compose_done.tmpl.hana");
const TEMPLATE_EMIT: &str = include_str!("templates/compose_emit.tmpl.hana");
const TEMPLATE_EMIT_STATIC: &str = include_str!("templates/compose_emit_static.tmpl.hana");
const TEMPLATE_ACCEPT: &str = include_str!("templates/compose_accept.tmpl.hana");
const TEMPLATE_ACCEPT_STATIC: &str = include_str!("templates/compose_accept_static.tmpl.hana");

fn compose_concurrent(args: &[Path]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 3 {
        return Err("compose_concurrent requires exactly 3 arguments".to_string());
    }
    let p1 = adjust_path(&args[0]);
    let p2 = adjust_path(&args[1]);
    let sync_fn = adjust_path(&args[2]);

    compile_template(TEMPLATE_CONCURRENT, &[
        ("p1", &p1),
        ("p2", &p2),
        ("sync_fn", &sync_fn),
    ])
}

fn compose_hidden(args: &[Path]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 2 {
        return Err("compose_hidden requires exactly 2 arguments".to_string());
    }
    let concurrent = adjust_path(&args[0]);
    let hidden_fn = adjust_path(&args[1]);

    compile_template(TEMPLATE_HIDDEN, &[
        ("concurrent", &concurrent),
        ("hidden_fn", &hidden_fn),
    ])
}

fn compose_prefix(args: &[Path]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 2 {
        return Err("compose_prefix requires exactly 2 arguments: target_machine and prefix_symbol".to_string());
    }
    let target = adjust_path(&args[0]);
    let prefix = adjust_path(&args[1]);

    compile_template(TEMPLATE_PREFIX, &[
        ("target", &target),
        ("prefix", &prefix),
    ])
}

fn compose_rename_prefix(args: &[Path]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 3 {
        return Err("compose_rename_prefix requires exactly 3 arguments: from_symbol, to_symbol, and target_machine".to_string());
    }
    let from_symbol = adjust_path(&args[0]);
    let to_symbol = adjust_path(&args[1]);
    let target = adjust_path(&args[2]);

    compile_template(TEMPLATE_RENAME_PREFIX, &[
        ("from_symbol", &from_symbol),
        ("to_symbol", &to_symbol),
        ("target", &target),
    ])
}

fn compose_static_closure(args: &[ResolvedArg]) -> Result<Vec<TopLevelItem>, String> {
    if args.len() != 2 {
        return Err("compose_static_closure requires exactly 2 arguments: target_machine and a value".to_string());
    }
    let machine = match &args[0] {
        ResolvedArg::Path(path) => adjust_path(path),
        _ => return Err("compose_static_closure: first argument must be a machine module path".to_string()),
    };
    let val = match &args[1] {
        ResolvedArg::Value(val) => val.clone(),
        ResolvedArg::Path(path) => ParsedValue::SymbolRef(adjust_path(path)),
    };

    compile_template(TEMPLATE_STATIC_CLOSURE, &[
        ("machine", &machine),
        ("val", &val),
    ])
}

fn compose_done() -> Result<Vec<TopLevelItem>, String> {
    compile_template(TEMPLATE_DONE, &[])
}

fn compose_emit_helper(val: Option<ParsedValue>, target: &Path) -> Result<Vec<TopLevelItem>, String> {
    let machine = adjust_path(target);
    match val {
        Some(v) => {
            compile_template(TEMPLATE_EMIT_STATIC, &[
                ("machine", &machine),
                ("val", &v),
            ])
        }
        None => {
            compile_template(TEMPLATE_EMIT, &[
                ("machine", &machine),
            ])
        }
    }
}

fn compose_accept_helper(val_set_path: Path, target: &Path) -> Result<Vec<TopLevelItem>, String> {
    let machine = adjust_path(target);

    compile_template(TEMPLATE_ACCEPT, &[
        ("machine", &machine),
        ("val_set_path", &val_set_path),
    ])
}

fn compose_accept_static_helper(val: ParsedValue, target: &Path) -> Result<Vec<TopLevelItem>, String> {
    let machine = adjust_path(target);

    compile_template(TEMPLATE_ACCEPT_STATIC, &[
        ("machine", &machine),
        ("val", &val),
    ])
}

fn generate_composition_items(
    composer: &str,
    args: &[ResolvedArg],
) -> Result<Vec<TopLevelItem>, String> {
    match composer {
        "compose_concurrent" => {
            let paths = extract_paths(args, "compose_concurrent")?;
            compose_concurrent(&paths)
        }
        "compose_hidden" => {
            let paths = extract_paths(args, "compose_hidden")?;
            compose_hidden(&paths)
        }
        "compose_prefix" => {
            let paths = extract_paths(args, "compose_prefix")?;
            compose_prefix(&paths)
        }
        "compose_rename_prefix" => {
            let paths = extract_paths(args, "compose_rename_prefix")?;
            compose_rename_prefix(&paths)
        }
        "compose_static_closure" => compose_static_closure(args),
        "compose_done" => {
            if !args.is_empty() {
                return Err("compose_done expects 0 arguments".to_string());
            }
            compose_done()
        }
        "compose_emit" => {
            let paths = extract_paths(args, "compose_emit")?;
            if paths.len() != 1 {
                return Err("compose_emit expects exactly 1 target machine argument".to_string());
            }
            compose_emit_helper(None, &paths[0])
        }
        "compose_emit_static" => {
            if args.len() != 2 {
                return Err("compose_emit_static expects exactly 2 arguments: event and target_machine".to_string());
            }
            let val = match &args[0] {
                ResolvedArg::Value(val) => val.clone(),
                ResolvedArg::Path(path) => ParsedValue::SymbolRef(adjust_path(path)),
            };
            let paths = extract_paths(&args[1..2], "compose_emit_static")?;
            compose_emit_helper(Some(val), &paths[0])
        }
        "compose_accept" => {
            if args.len() != 2 {
                return Err("compose_accept expects exactly 2 arguments: value_set and target_machine".to_string());
            }
            let val_set_path = match &args[0] {
                ResolvedArg::Path(path) => adjust_path(path),
                _ => return Err("compose_accept: first argument must be a sentence path".to_string()),
            };
            let paths = extract_paths(&args[1..2], "compose_accept")?;
            compose_accept_helper(val_set_path, &paths[0])
        }
        "compose_accept_static" => {
            if args.len() != 2 {
                return Err("compose_accept_static expects exactly 2 arguments: event and target_machine".to_string());
            }
            let val = match &args[0] {
                ResolvedArg::Value(val) => val.clone(),
                ResolvedArg::Path(path) => ParsedValue::SymbolRef(adjust_path(path)),
            };
            let paths = extract_paths(&args[1..2], "compose_accept_static")?;
            compose_accept_static_helper(val, &paths[0])
        }
        _ => Err(format!("Unknown composer: {}", composer)),
    }
}

struct Compiler<'a> {
    tree: &'a ModuleTree,
    sentences: Vec<Vec<Instruction>>,
    names: Vec<String>,
    annotations: Vec<Vec<Annotation>>,
    current_parent_idx: Option<SentenceIndex>,
}

impl<'a> Compiler<'a> {
    fn compile_value(&self, scope: ModuleId, parsed: ParsedValue) -> Result<Value, String> {
        match parsed {
            ParsedValue::Bool(b) => Ok(Value::Bool(b)),
            ParsedValue::Int(i) => Ok(Value::Int(i)),
            ParsedValue::Float(f) => Ok(Value::Float(f)),
            ParsedValue::Tuple(elements) => {
                let mut compiled_elements = Vec::new();
                for elem in elements {
                    compiled_elements.push(self.compile_value(scope, elem)?);
                }
                Ok(Value::Tuple(compiled_elements))
            }
            ParsedValue::SymbolRef(path) => {
                match self.tree.resolve(scope, &path)? {
                    ResolvedItem::Symbol(val) => Ok(val),
                    ResolvedItem::Sentence(_) => Err(format!("Expected symbol, found sentence at path {:?}", path)),
                }
            }
        }
    }

    fn compile_sentence_body(&mut self, scope: ModuleId, instructions: Vec<ParsedInstruction>) -> Result<Vec<Instruction>, String> {
        let mut compiled = Vec::new();
        for inst in instructions {
            let c_inst = match inst {
                ParsedInstruction::Push(v) => {
                    let compiled_val = self.compile_value(scope, v)?;
                    Instruction::Push(compiled_val)
                }
                ParsedInstruction::Drop(d) => Instruction::Drop(d),
                ParsedInstruction::Pick(d) => Instruction::Pick(d),
                ParsedInstruction::Roll(d) => Instruction::Roll(d),
                ParsedInstruction::Equal => Instruction::Equal,
                ParsedInstruction::Greater => Instruction::Greater,
                ParsedInstruction::Less => Instruction::Less,
                ParsedInstruction::Add => Instruction::Add,
                ParsedInstruction::Subtract => Instruction::Subtract,
                ParsedInstruction::Multiply => Instruction::Multiply,
                ParsedInstruction::Divide => Instruction::Divide,
                ParsedInstruction::Modulo => Instruction::Modulo,
                ParsedInstruction::Not => Instruction::Not,
                ParsedInstruction::Negate => Instruction::Negate,
                ParsedInstruction::Print => Instruction::Print,
                ParsedInstruction::Panic => Instruction::Panic,
                ParsedInstruction::Assert => Instruction::Assert,
                ParsedInstruction::AssertEqual => Instruction::AssertEqual,
                ParsedInstruction::Tuple(n) => Instruction::Tuple(n),
                ParsedInstruction::Untuple(n) => Instruction::Untuple(n),
                ParsedInstruction::And => Instruction::And,
                ParsedInstruction::Or => Instruction::Or,
                ParsedInstruction::SymbolLen => Instruction::SymbolLen,
                ParsedInstruction::SymbolCharAt => Instruction::SymbolCharAt,
                ParsedInstruction::IsInt => Instruction::IsInt,
                ParsedInstruction::IsBool => Instruction::IsBool,
                ParsedInstruction::IsFloat => Instruction::IsFloat,
                ParsedInstruction::IsSymbol => Instruction::IsSymbol,
                ParsedInstruction::IsTuple => Instruction::IsTuple,
                ParsedInstruction::TupleLength => Instruction::TupleLength,
                ParsedInstruction::Jump(target) => {
                    let target_idx = self.resolve_target(scope, target)?;
                    Instruction::Jump(target_idx)
                }
                ParsedInstruction::Branch(t1, t2) => {
                    let idx1 = self.resolve_target(scope, t1)?;
                    let idx2 = self.resolve_target(scope, t2)?;
                    Instruction::Branch(idx1, idx2)
                }
                ParsedInstruction::TypeCheckPath(path) => {
                    let resolved = match self.tree.resolve(scope, &path) {
                        Ok(res) => res,
                        Err(e) => {
                            let mut check_path = path.clone();
                            check_path.segments.push(PathSegment::Identifier("check".to_string()));
                            self.tree.resolve(scope, &check_path)
                                .map_err(|_| format!("Could not resolve type path '{}': {}", path, e))?
                        }
                    };
                    match resolved {
                        ResolvedItem::Sentence(idx) => {
                            Instruction::Jump(idx)
                        }
                        ResolvedItem::Symbol(val) => {
                            compiled.push(Instruction::Push(val));
                            Instruction::Equal
                        }
                    }
                }
            };
            compiled.push(c_inst);
        }
        Ok(compiled)
    }

    fn resolve_target(&mut self, scope: ModuleId, target: Target) -> Result<SentenceIndex, String> {
        match target {
            Target::Label(path) => {
                match self.tree.resolve(scope, &path).map_err(|e| format!("Unresolved label target: {}", e))? {
                    ResolvedItem::Sentence(idx) => Ok(idx),
                    ResolvedItem::Symbol(_) => Err(format!("Expected sentence, found symbol at path {:?}", path)),
                }
            }
            Target::Inline(parsed_sentence) => {
                let new_idx = SentenceIndex::from(self.sentences.len());
                self.sentences.push(Vec::new());
                self.names.push("<inline>".to_string());

                let mut inline_anns = Vec::new();
                if let Some(parent_idx) = self.current_parent_idx {
                    let parent_idx_usize: usize = parent_idx.into();
                    if parent_idx_usize < self.annotations.len() {
                        if self.annotations[parent_idx_usize].iter().any(|ann| matches!(ann, Annotation::Recursive)) {
                            inline_anns.push(Annotation::Recursive);
                        }
                    }
                }
                self.annotations.push(inline_anns);

                let prev_parent = self.current_parent_idx;
                self.current_parent_idx = Some(new_idx);
                let compiled_body = self.compile_sentence_body(scope, parsed_sentence.instructions);
                self.current_parent_idx = prev_parent;

                let compiled_body = compiled_body?;
                let idx_usize: usize = new_idx.into();
                self.sentences[idx_usize] = compiled_body;
                Ok(new_idx)
            }
        }
    }
}

/// Assembles the input text into a `Library`.
pub fn assemble(input: &str) -> Result<Library, String> {
    assemble_with_path(input, None)
}

/// Assembles the input text with an optional base directory context for resolving external modules.
pub fn assemble_with_path(input: &str, base_dir: Option<&std::path::Path>) -> Result<Library, String> {
    let tokens = tokenize(input)?;
    let mut stream = TokenStream { tokens, position: 0 };
    let items = parse_top_level(&mut stream, base_dir)?;

    let mut builder = TreeBuilder::new();
    builder.build(items, crate::resolve::ROOT)?;

    let TreeBuilder {
        tree,
        sentence_counter,
        flat_sentences,
        exports,
        tests,
        test_machines,
        ..
    } = builder;

    let mut compiler = Compiler {
        tree: &tree,
        sentences: Vec::new(),
        names: Vec::new(),
        annotations: Vec::new(),
        current_parent_idx: None,
    };

    // Pre-allocate space for all named sentences
    compiler.sentences.resize(sentence_counter, Vec::new());
    compiler.names.resize(sentence_counter, String::new());
    compiler.annotations.resize(sentence_counter, Vec::new());

    // Compile instructions recursively
    for (idx, (scope, sentence)) in flat_sentences.into_iter().enumerate() {
        compiler.annotations[idx] = sentence.annotations.clone();
        compiler.current_parent_idx = Some(SentenceIndex::from(idx));
        // A `type`/`enum` check is declared inside the module named after the
        // type, but its body names sibling types, so it resolves one level up.
        let resolve_scope = if sentence.is_type_check {
            tree.parent(scope)
                .ok_or_else(|| "Internal error: type check sentence declared at the crate root".to_string())?
        } else {
            scope
        };
        let compiled_instructions = compiler.compile_sentence_body(resolve_scope, sentence.body.instructions)?;
        compiler.sentences[idx] = compiled_instructions;
        compiler.names[idx] = tree.fq_name(scope, &sentence.name);
    }

    let mut library = Library::new();
    for s in compiler.sentences {
        library.sentences.push(s);
    }

    let mut final_annotations = typed_index_collections::TiVec::new();
    for ann in compiler.annotations {
        final_annotations.push(ann);
    }
    final_annotations.resize(library.sentences.len(), Vec::new());

    let mut final_names = typed_index_collections::TiVec::new();
    for n in compiler.names {
        final_names.push(n);
    }
    library.names = final_names;
    library.exports = exports;
    library.tests = tests;
    library.test_machines = test_machines;
    library.annotations = final_annotations;

    library.symbols = tree.symbol_map();

    crate::arity::check_arities(&mut library)?;

    Ok(library)
}
