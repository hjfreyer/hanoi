use std::collections::HashMap;
use crate::library::{Library, SentenceIndex};
use crate::opcode::Instruction;
use crate::value::Value;

/// Token types for the assembly lexer.
#[derive(Debug, Clone, PartialEq)]
enum Token {
    Export,
    Identifier(String),
    LBrace,
    RBrace,
    LParen,
    RParen,
    Comma,
    Colon,
    Int(i64),
    Float(f64),
    Nil,
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
            '#' => {
                // Comment, consume until end of line
                chars.next();
                while let Some(&next_c) = chars.peek() {
                    if next_c == '\n' {
                        break;
                    }
                    chars.next();
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
            ':' => {
                tokens.push(Token::Colon);
                chars.next();
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
                    "nil" => tokens.push(Token::Nil),
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

/// Recursively parse values (including nested tuples).
fn parse_value(stream: &mut TokenStream) -> Result<Value, String> {
    match stream.next() {
        Some(Token::Nil) => Ok(Value::Nil),
        Some(Token::Bool(b)) => Ok(Value::Bool(b)),
        Some(Token::Int(i)) => Ok(Value::Int(i)),
        Some(Token::Float(f)) => Ok(Value::Float(f)),
        Some(Token::LParen) => {
            let mut elements = Vec::new();
            if stream.peek() == Some(&Token::RParen) {
                stream.next(); // consume ')'
                return Ok(Value::Tuple(elements));
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
            Ok(Value::Tuple(elements))
        }
        Some(other) => Err(format!("Expected value, found {:?}", other)),
        None => Err("Expected value, found end of input".to_string()),
    }
}

/// Parses a target which is either a named label or an inline `{}` block.
fn parse_target(stream: &mut TokenStream) -> Result<Target, String> {
    match stream.peek() {
        Some(&Token::Identifier(_)) => {
            if let Some(Token::Identifier(name)) = stream.next() {
                Ok(Target::Label(name))
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
        other => Err(format!("Unknown instruction mnemonic: '{}'", other)),
    }
}

struct TopLevelSentence {
    is_exported: bool,
    name: String,
    body: ParsedSentence,
}

fn parse_top_level(stream: &mut TokenStream) -> Result<Vec<TopLevelSentence>, String> {
    let mut sentences = Vec::new();

    while stream.peek().is_some() {
        let is_exported = if stream.peek() == Some(&Token::Export) {
            stream.next();
            true
        } else {
            false
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

        sentences.push(TopLevelSentence {
            is_exported,
            name,
            body,
        });
    }

    Ok(sentences)
}

struct ParsedSentence {
    instructions: Vec<ParsedInstruction>,
}

enum Target {
    Label(String),
    Inline(ParsedSentence),
}

enum ParsedInstruction {
    Push(Value),
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
}

/// The result of parsing and compiling assembly code.
#[derive(Debug, Clone, PartialEq)]
pub struct AssemblyResult {
    /// The compiled bytecode library.
    pub library: Library,
    /// Maps exported sentence label names to their SentenceIndex.
    pub exports: HashMap<String, SentenceIndex>,
}

struct Compiler {
    label_map: HashMap<String, SentenceIndex>,
    sentences: Vec<Vec<Instruction>>,
    exports: HashMap<String, SentenceIndex>,
}

impl Compiler {
    fn compile_sentence_body(&mut self, instructions: Vec<ParsedInstruction>) -> Result<Vec<Instruction>, String> {
        let mut compiled = Vec::new();
        for inst in instructions {
            let c_inst = match inst {
                ParsedInstruction::Push(v) => Instruction::Push(v),
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
                ParsedInstruction::Jump(target) => {
                    let target_idx = self.resolve_target(target)?;
                    Instruction::Jump(target_idx)
                }
                ParsedInstruction::Branch(t1, t2) => {
                    let idx1 = self.resolve_target(t1)?;
                    let idx2 = self.resolve_target(t2)?;
                    Instruction::Branch(idx1, idx2)
                }
            };
            compiled.push(c_inst);
        }
        Ok(compiled)
    }

    fn resolve_target(&mut self, target: Target) -> Result<SentenceIndex, String> {
        match target {
            Target::Label(name) => {
                self.label_map.get(&name)
                    .copied()
                    .ok_or_else(|| format!("Unresolved label target: {}", name))
            }
            Target::Inline(parsed_sentence) => {
                let new_idx = SentenceIndex::from(self.sentences.len());
                self.sentences.push(Vec::new());
                let compiled_body = self.compile_sentence_body(parsed_sentence.instructions)?;
                let idx_usize: usize = new_idx.into();
                self.sentences[idx_usize] = compiled_body;
                Ok(new_idx)
            }
        }
    }
}

/// Assembles the input text into a `Library` and export mappings.
pub fn assemble(input: &str) -> Result<AssemblyResult, String> {
    let tokens = tokenize(input)?;
    let mut stream = TokenStream { tokens, position: 0 };
    let top_level = parse_top_level(&mut stream)?;

    let mut compiler = Compiler {
        label_map: HashMap::new(),
        sentences: Vec::new(),
        exports: HashMap::new(),
    };

    // Pass 1: Map top-level names to their index
    for (idx, sentence) in top_level.iter().enumerate() {
        let s_idx = SentenceIndex::from(idx);
        if compiler.label_map.insert(sentence.name.clone(), s_idx).is_some() {
            return Err(format!("Duplicate sentence name: {}", sentence.name));
        }
        if sentence.is_exported {
            compiler.exports.insert(sentence.name.clone(), s_idx);
        }
    }

    // Pre-allocate space for top-level sentences
    compiler.sentences.resize(top_level.len(), Vec::new());

    // Pass 2: Compile instructions recursively (handles inline sentences)
    for (idx, sentence) in top_level.into_iter().enumerate() {
        let compiled_instructions = compiler.compile_sentence_body(sentence.body.instructions)?;
        compiler.sentences[idx] = compiled_instructions;
    }

    let mut library = Library::new();
    for s in compiler.sentences {
        library.sentences.push(s);
    }

    Ok(AssemblyResult {
        library,
        exports: compiler.exports,
    })
}
