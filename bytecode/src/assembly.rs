use std::collections::{HashMap, HashSet};
use crate::library::{Library, SentenceIndex, Annotation};
use crate::opcode::Instruction;
use crate::value::{Value, Symbol};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathSegment {
    Crate,
    Super,
    Identifier(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path {
    pub segments: Vec<PathSegment>,
}

/// Token types for the assembly lexer.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Export,
    SymbolKeyword,
    TestKeyword,
    ModKeyword,
    SentenceKeyword,
    FunctionKeyword,
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
                "safety" => {
                    stream.expect(Token::LParen)?;
                    let formula_str = match stream.next() {
                        Some(Token::StringLiteral(s)) => s,
                        Some(other) => return Err(format!("Expected string literal for safety formula, found {:?}", other)),
                        None => return Err("Expected string literal for safety formula, found end of input".to_string()),
                    };
                    stream.expect(Token::RParen)?;
                    Annotation::Safety(formula_str)
                }
                "behavior" => {
                    stream.expect(Token::LParen)?;
                    let formula_str = match stream.next() {
                        Some(Token::StringLiteral(s)) => s,
                        Some(other) => return Err(format!("Expected string literal for behavior formula, found {:?}", other)),
                        None => return Err("Expected string literal for behavior formula, found end of input".to_string()),
                    };
                    stream.expect(Token::RParen)?;
                    Annotation::Behavior(formula_str)
                }
                "z3ify" => {
                    Annotation::Z3ify
                }
                "recursive" => {
                    Annotation::Recursive
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

            let is_function = if stream.peek() == Some(&Token::SentenceKeyword) {
                stream.next();
                false
            } else if stream.peek() == Some(&Token::FunctionKeyword) {
                stream.next();
                true
            } else {
                return Err(format!("Expected 'sentence' or 'function', found {:?}", stream.peek()));
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

            let is_function = if stream.peek() == Some(&Token::SentenceKeyword) {
                stream.next();
                false
            } else if stream.peek() == Some(&Token::FunctionKeyword) {
                stream.next();
                true
            } else {
                return Err(format!("Expected 'sentence' or 'function', found {:?}", stream.peek()));
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
            }));
        }
        }
    }

    Ok(items)
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
}



struct Module {
    name: String,
    symbols: HashMap<String, Value>,
    sentences: HashMap<String, SentenceIndex>,
    submodules: HashMap<String, Module>,
}

impl Module {
    fn new(name: String) -> Self {
        Self {
            name,
            symbols: HashMap::new(),
            sentences: HashMap::new(),
            submodules: HashMap::new(),
        }
    }
}

fn build_module_tree(
    items: Vec<TopLevelItem>,
    current_path: &mut Vec<String>,
    symbol_counter: &mut usize,
    sentence_counter: &mut usize,
    module: &mut Module,
    flat_sentences: &mut Vec<(Vec<String>, TopLevelSentence)>,
    exports: &mut HashMap<String, SentenceIndex>,
    tests: &mut HashMap<String, SentenceIndex>,
    test_machines: &mut HashSet<String>,
) -> Result<(), String> {
    let mut anon_counter = 0;
    build_module_tree_impl(
        items,
        current_path,
        symbol_counter,
        sentence_counter,
        module,
        flat_sentences,
        exports,
        tests,
        test_machines,
        &mut anon_counter,
    )
}

fn resolve_module_expr(
    expr: &ModuleExpr,
    current_path: &mut Vec<String>,
    symbol_counter: &mut usize,
    sentence_counter: &mut usize,
    parent_module: &mut Module,
    flat_sentences: &mut Vec<(Vec<String>, TopLevelSentence)>,
    exports: &mut HashMap<String, SentenceIndex>,
    tests: &mut HashMap<String, SentenceIndex>,
    test_machines: &mut HashSet<String>,
    anon_counter: &mut usize,
) -> Result<ResolvedArg, String> {
    match expr {
        ModuleExpr::Named(path) => Ok(ResolvedArg::Path(path.clone())),
        ModuleExpr::Value(val) => Ok(ResolvedArg::Value(val.clone())),
        ModuleExpr::Composer { composer, args } => {
            let mut resolved_args = Vec::new();
            for arg in args {
                resolved_args.push(resolve_module_expr(
                    arg,
                    current_path,
                    symbol_counter,
                    sentence_counter,
                    parent_module,
                    flat_sentences,
                    exports,
                    tests,
                    test_machines,
                    anon_counter,
                )?);
            }
            let generated_items = generate_composition_items(composer, &resolved_args)?;
            let anon_name = format!("__anon_mod_{}", anon_counter);
            *anon_counter += 1;

            let mut anon_submodule = Module::new(anon_name.clone());
            current_path.push(anon_name.clone());
            build_module_tree_impl(
                generated_items,
                current_path,
                symbol_counter,
                sentence_counter,
                &mut anon_submodule,
                flat_sentences,
                exports,
                tests,
                test_machines,
                anon_counter,
            )?;
            current_path.pop();

            parent_module.submodules.insert(anon_name.clone(), anon_submodule);

            Ok(ResolvedArg::Path(Path {
                segments: vec![PathSegment::Identifier(anon_name)],
            }))
        }
    }
}

fn build_module_tree_impl(
    items: Vec<TopLevelItem>,
    current_path: &mut Vec<String>,
    symbol_counter: &mut usize,
    sentence_counter: &mut usize,
    module: &mut Module,
    flat_sentences: &mut Vec<(Vec<String>, TopLevelSentence)>,
    exports: &mut HashMap<String, SentenceIndex>,
    tests: &mut HashMap<String, SentenceIndex>,
    test_machines: &mut HashSet<String>,
    anon_counter: &mut usize,
) -> Result<(), String> {
    for item in items {
        match item {
            TopLevelItem::SymbolDecl { name, debug_desc } => {
                if name == "crate" || name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", name));
                }

                if module.symbols.contains_key(&name)
                    || module.sentences.contains_key(&name)
                    || module.submodules.contains_key(&name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", name, module.name));
                }

                let fq_name = if current_path.is_empty() {
                    name.clone()
                } else {
                    format!("{}::{}", current_path.join("::"), name)
                };

                let desc = debug_desc.unwrap_or(fq_name);
                let symbol = Value::Symbol(Symbol {
                    id: *symbol_counter,
                    name: desc,
                });
                *symbol_counter += 1;

                module.symbols.insert(name, symbol);
            }
            TopLevelItem::Sentence(s) => {
                if s.name == "crate" || s.name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", s.name));
                }

                if module.symbols.contains_key(&s.name)
                    || module.sentences.contains_key(&s.name)
                    || module.submodules.contains_key(&s.name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", s.name, module.name));
                }

                let s_idx = SentenceIndex::from(*sentence_counter);
                *sentence_counter += 1;

                module.sentences.insert(s.name.clone(), s_idx);

                let fq_name = if current_path.is_empty() {
                    s.name.clone()
                } else {
                    format!("{}::{}", current_path.join("::"), s.name)
                };

                if s.is_exported {
                    exports.insert(fq_name.clone(), s_idx);
                }
                if s.is_test {
                    tests.insert(fq_name.clone(), s_idx);
                }

                flat_sentences.push((current_path.clone(), s));
            }
            TopLevelItem::Mod { name, items: mod_items, is_test } => {
                if name == "crate" || name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", name));
                }

                if module.symbols.contains_key(&name)
                    || module.sentences.contains_key(&name)
                    || module.submodules.contains_key(&name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", name, module.name));
                }

                let mut submodule = Module::new(name.clone());
                current_path.push(name.clone());
                build_module_tree_impl(
                    mod_items,
                    current_path,
                    symbol_counter,
                    sentence_counter,
                    &mut submodule,
                    flat_sentences,
                    exports,
                    tests,
                    test_machines,
                    anon_counter,
                )?;

                let mod_fq_path = current_path.join("::");
                if is_test {
                    let _init_idx = submodule.sentences.get("init")
                        .copied()
                        .ok_or_else(|| format!("Test mod '{}' must export an 'init' sentence", mod_fq_path))?;
                    test_machines.insert(mod_fq_path);
                }

                current_path.pop();

                module.submodules.insert(name, submodule);
            }
            TopLevelItem::Compose { name, composer, args, is_test } => {
                if name == "crate" || name == "super" {
                    return Err(format!("Cannot use reserved keyword '{}' as name", name));
                }

                if module.symbols.contains_key(&name)
                    || module.sentences.contains_key(&name)
                    || module.submodules.contains_key(&name)
                {
                    return Err(format!("Duplicate declaration of name '{}' in module '{}'", name, module.name));
                }

                let mut resolved_args = Vec::new();
                for arg in &args {
                    resolved_args.push(resolve_module_expr(
                        arg,
                        current_path,
                        symbol_counter,
                        sentence_counter,
                        module,
                        flat_sentences,
                        exports,
                        tests,
                        test_machines,
                        anon_counter,
                    )?);
                }

                let generated_items = generate_composition_items(&composer, &resolved_args)?;
                let mut submodule = Module::new(name.clone());
                current_path.push(name.clone());
                build_module_tree_impl(
                    generated_items,
                    current_path,
                    symbol_counter,
                    sentence_counter,
                    &mut submodule,
                    flat_sentences,
                    exports,
                    tests,
                    test_machines,
                    anon_counter,
                )?;

                let mod_fq_path = current_path.join("::");
                if is_test {
                    let _init_idx = submodule.sentences.get("init")
                        .copied()
                        .ok_or_else(|| format!("Test mod '{}' must export an 'init' sentence", mod_fq_path))?;
                    test_machines.insert(mod_fq_path.clone());

                    for sentence_name in &["init", "accept", "emit", "process", "tau_reduce", "is_done", "is_ready_to_finish"] {
                        if let Some(&s_idx) = submodule.sentences.get(*sentence_name) {
                            let fq_sentence_name = format!("{}::{}", mod_fq_path, sentence_name);
                            exports.insert(fq_sentence_name, s_idx);
                        }
                    }
                }

                current_path.pop();

                module.submodules.insert(name, submodule);
            }
        }
    }
    Ok(())
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

impl std::fmt::Display for PathSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PathSegment::Crate => write!(f, "crate"),
            PathSegment::Super => write!(f, "super"),
            PathSegment::Identifier(name) => write!(f, "{}", name),
        }
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let segs: Vec<String> = self.segments.iter().map(|s| s.to_string()).collect();
        write!(f, "{}", segs.join("::"))
    }
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

enum ResolvedItem {
    Symbol(Value),
    Sentence(SentenceIndex),
}

struct Compiler<'a> {
    root_module: &'a Module,
    sentences: Vec<Vec<Instruction>>,
    names: Vec<String>,
    annotations: Vec<Vec<Annotation>>,
    current_parent_idx: Option<SentenceIndex>,
}

impl<'a> Compiler<'a> {
    fn resolve_path(&self, current_path: &[String], path: &Path) -> Result<ResolvedItem, String> {
        let mut curr_node = self.root_module;
        let mut segments_iter = path.segments.iter().peekable();

        if let Some(first) = segments_iter.peek() {
            match first {
                PathSegment::Crate => {
                    segments_iter.next();
                    // curr_node is already root_module
                }
                PathSegment::Super => {
                    let mut up_count = 0;
                    while let Some(PathSegment::Super) = segments_iter.peek() {
                        segments_iter.next();
                        up_count += 1;
                    }
                    if up_count > current_path.len() {
                        return Err(format!("Path goes up too many levels (current path depth: {})", current_path.len()));
                    }
                    let target_depth = current_path.len() - up_count;
                    let target_path = &current_path[..target_depth];
                    for name in target_path {
                        curr_node = curr_node.submodules.get(name)
                            .ok_or_else(|| format!("Internal error: submodule '{}' not found in path navigation", name))?;
                    }
                }
                PathSegment::Identifier(_) => {
                    for name in current_path {
                        curr_node = curr_node.submodules.get(name)
                            .ok_or_else(|| format!("Internal error: submodule '{}' not found in path navigation", name))?;
                    }
                }
            }
        }

        let mut last_name: Option<&str> = None;
        while let Some(seg) = segments_iter.next() {
            match seg {
                PathSegment::Crate => return Err("'crate' can only appear at the beginning of a path".to_string()),
                PathSegment::Super => return Err("'super' can only appear at the beginning of a path".to_string()),
                PathSegment::Identifier(name) => {
                    if segments_iter.peek().is_none() {
                        last_name = Some(name);
                    } else {
                        if let Some(sub) = curr_node.submodules.get(name) {
                            curr_node = sub;
                        } else {
                            return Err(format!("Module '{}' not found in '{}'", name, curr_node.name));
                        }
                    }
                }
            }
        }

        let last_name = last_name.ok_or_else(|| "Empty path after navigation".to_string())?;

        if let Some(val) = curr_node.symbols.get(last_name) {
            Ok(ResolvedItem::Symbol(val.clone()))
        } else if let Some(&idx) = curr_node.sentences.get(last_name) {
            Ok(ResolvedItem::Sentence(idx))
        } else {
            Err(format!("Item '{}' not found in module '{}'", last_name, curr_node.name))
        }
    }

    fn compile_value(&self, current_path: &[String], parsed: ParsedValue) -> Result<Value, String> {
        match parsed {
            ParsedValue::Bool(b) => Ok(Value::Bool(b)),
            ParsedValue::Int(i) => Ok(Value::Int(i)),
            ParsedValue::Float(f) => Ok(Value::Float(f)),
            ParsedValue::Tuple(elements) => {
                let mut compiled_elements = Vec::new();
                for elem in elements {
                    compiled_elements.push(self.compile_value(current_path, elem)?);
                }
                Ok(Value::Tuple(compiled_elements))
            }
            ParsedValue::SymbolRef(path) => {
                match self.resolve_path(current_path, &path)? {
                    ResolvedItem::Symbol(val) => Ok(val),
                    ResolvedItem::Sentence(_) => Err(format!("Expected symbol, found sentence at path {:?}", path)),
                }
            }
        }
    }

    fn compile_sentence_body(&mut self, current_path: &[String], instructions: Vec<ParsedInstruction>) -> Result<Vec<Instruction>, String> {
        let mut compiled = Vec::new();
        for inst in instructions {
            let c_inst = match inst {
                ParsedInstruction::Push(v) => {
                    let compiled_val = self.compile_value(current_path, v)?;
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
                    let target_idx = self.resolve_target(current_path, target)?;
                    Instruction::Jump(target_idx)
                }
                ParsedInstruction::Branch(t1, t2) => {
                    let idx1 = self.resolve_target(current_path, t1)?;
                    let idx2 = self.resolve_target(current_path, t2)?;
                    Instruction::Branch(idx1, idx2)
                }
            };
            compiled.push(c_inst);
        }
        Ok(compiled)
    }

    fn resolve_target(&mut self, current_path: &[String], target: Target) -> Result<SentenceIndex, String> {
        match target {
            Target::Label(path) => {
                match self.resolve_path(current_path, &path).map_err(|e| format!("Unresolved label target: {}", e))? {
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
                let compiled_body = self.compile_sentence_body(current_path, parsed_sentence.instructions);
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

fn collect_symbols(module: &Module, current_path: &mut Vec<String>, symbols_map: &mut HashMap<String, Value>) {
    for (name, symbol) in &module.symbols {
        let fq_name = if current_path.is_empty() {
            name.clone()
        } else {
            format!("{}::{}", current_path.join("::"), name)
        };
        symbols_map.insert(fq_name, symbol.clone());
    }

    for (sub_name, sub_module) in &module.submodules {
        current_path.push(sub_name.clone());
        collect_symbols(sub_module, current_path, symbols_map);
        current_path.pop();
    }
}

/// Assembles the input text with an optional base directory context for resolving external modules.
pub fn assemble_with_path(input: &str, base_dir: Option<&std::path::Path>) -> Result<Library, String> {
    let tokens = tokenize(input)?;
    let mut stream = TokenStream { tokens, position: 0 };
    let items = parse_top_level(&mut stream, base_dir)?;

    let mut root_module = Module::new("crate".to_string());
    let mut symbol_counter = 0;
    let mut sentence_counter = 0;
    let mut flat_sentences = Vec::new();
    let mut exports = HashMap::new();
    let mut tests = HashMap::new();
    let mut test_machines = HashSet::new();

    let mut current_path = Vec::new();
    build_module_tree(
        items,
        &mut current_path,
        &mut symbol_counter,
        &mut sentence_counter,
        &mut root_module,
        &mut flat_sentences,
        &mut exports,
        &mut tests,
        &mut test_machines,
    )?;

    let mut compiler = Compiler {
        root_module: &root_module,
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
    for (idx, (path, sentence)) in flat_sentences.into_iter().enumerate() {
        compiler.annotations[idx] = sentence.annotations.clone();
        compiler.current_parent_idx = Some(SentenceIndex::from(idx));
        let compiled_instructions = compiler.compile_sentence_body(&path, sentence.body.instructions)?;
        compiler.sentences[idx] = compiled_instructions;
        let fq_name = if path.is_empty() {
            sentence.name.clone()
        } else {
            format!("{}::{}", path.join("::"), sentence.name)
        };
        compiler.names[idx] = fq_name;
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

    let mut symbols_map = HashMap::new();
    let mut path_tracker = Vec::new();
    collect_symbols(&root_module, &mut path_tracker, &mut symbols_map);
    library.symbols = symbols_map;

    crate::arity::check_arities(&mut library)?;
    crate::safety::check_safety(&library)?;

    Ok(library)
}
