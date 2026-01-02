use std::{collections::VecDeque, path::PathBuf};

use pest::{Parser, iterators::Pair};
use pest_derive::Parser;

use source::{Loader, Sources};

use itertools::Itertools;
use typed_index_collections::TiVec;

use crate::{bytecode, parser::source::FileIndex};

pub mod source;

#[derive(Parser)]
#[grammar = "parser/hanoi.pest"]

struct HanoiParser;

pub fn load_all(loader: &Loader) -> anyhow::Result<(Sources, Library)> {
    let mut sources = Sources::default();
    let mut queue: VecDeque<Vec<source::Span>> = VecDeque::from([vec![]]);
    let mut library = Library::default();
    while let Some(mod_path) = queue.pop_front() {
        let mod_name: PathBuf = mod_path.iter().map(|span| span.as_str(&sources)).collect();
        let file_idx = loader.load(mod_name, &mut sources)?;
        let factory = Factory(file_idx);

        let parsed = HanoiParser::parse(Rule::file, &sources.files[file_idx].source)?
            .next()
            .unwrap();
        let file = factory.file(mod_path.clone(), parsed);

        for import in file.imports.iter() {
            let sub_path = mod_path.iter().cloned().chain([import.0]).collect();
            queue.push_back(sub_path);
        }

        library.files.push(file);
    }

    Ok((sources, library))
}

#[derive(Debug, Default, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Library {
    pub files: TiVec<FileIndex, File>,
}

struct Factory(FileIndex);

impl Factory {
    fn file(&self, mod_path: Vec<source::Span>, p: Pair<Rule>) -> File {
        assert_eq!(p.as_rule(), Rule::file_body);
        let pairs = p.into_inner();
        let mut result = File {
            mod_path,
            imports: vec![],
            namespace: Namespace::default(),
        };
        for pair in pairs {
            match pair.as_rule() {
                Rule::external_mod_decl => result
                    .imports
                    .push(self.identifier(pair.into_inner().exactly_one().unwrap())),
                Rule::decl => result.namespace.decls.push(self.decl(pair)),
                _ => panic!("invalid file item: {:?}", pair.as_rule()),
            }
        }
        result
    }

    fn decl(&self, p: Pair<Rule>) -> Decl {
        assert_eq!(p.as_rule(), Rule::decl);
        let inner = p.into_inner().exactly_one().unwrap();
        match inner.as_rule() {
            Rule::const_decl => Decl::ConstDecl(self.const_decl(inner)),
            Rule::sentence_decl => Decl::SentenceDecl(self.sentence_decl(inner)),
            Rule::mod_decl => Decl::ModuleDecl(self.module_decl(inner)),
            _ => panic!("invalid decl: {:?}", inner.as_rule()),
        }
    }

    fn module_decl(&self, p: Pair<Rule>) -> ModuleDecl {
        assert_eq!(p.as_rule(), Rule::mod_decl);
        let (name, namespace) = p.into_inner().collect_tuple().unwrap();
        ModuleDecl {
            name: self.identifier(name),
            namespace: self.namespace(namespace),
        }
    }

    fn namespace(&self, p: Pair<Rule>) -> Namespace {
        assert_eq!(p.as_rule(), Rule::namespace);
        let pairs = p.into_inner();
        let mut result = Namespace::default();
        for pair in pairs {
            result.decls.push(self.decl(pair));
        }
        result
    }

    fn const_decl(&self, p: Pair<Rule>) -> ConstDecl {
        assert_eq!(p.as_rule(), Rule::const_decl);
        let (name, expr) = p.into_inner().collect_tuple().unwrap();
        ConstDecl {
            name: self.identifier(name),
            value: self.const_expr(expr),
        }
    }

    fn const_expr(&self, p: Pair<Rule>) -> ConstExpr {
        assert_eq!(p.as_rule(), Rule::const_expr);
        let inner = p.into_inner().exactly_one().unwrap();

        match inner.as_rule() {
            Rule::literal => ConstExpr::Literal(self.literal(inner)),
            Rule::path => ConstExpr::Path(self.path(inner)),
            _ => panic!("invalid const expr"),
        }
    }

    fn sentence_decl(&self, p: Pair<Rule>) -> SentenceDecl {
        assert_eq!(p.as_rule(), Rule::sentence_decl);
        let span = source::Span::from_ast(self.0, p.as_span());
        let (name, sentence) = p.into_inner().collect_tuple().unwrap();
        let name = self.identifier(name);
        let sentence = self.sentence(sentence);
        SentenceDecl {
            span,
            name,
            sentence,
        }
    }

    fn sentence(&self, p: Pair<Rule>) -> Sentence {
        assert_eq!(p.as_rule(), Rule::sentence);
        let span = source::Span::from_ast(self.0, p.as_span());
        let words = p.into_inner().map(|p| self.word(p)).collect();
        Sentence { span, words }
    }

    fn word(&self, p: Pair<Rule>) -> Word {
        assert_eq!(p.as_rule(), Rule::raw_word);
        let span = source::Span::from_ast(self.0, p.as_span());
        let (operator, args) = p.into_inner().collect_tuple().unwrap();
        let operator = self.identifier(operator);
        let args = args.into_inner().map(|p| self.word_arg(p)).collect();
        Word {
            span,
            operator,
            args,
        }
    }

    fn word_arg(&self, p: Pair<Rule>) -> WordArg {
        assert_eq!(p.as_rule(), Rule::word_arg);
        let inner = p.into_inner().exactly_one().unwrap();
        match inner.as_rule() {
            Rule::literal => WordArg::Literal(self.literal(inner)),
            Rule::path => WordArg::Path(self.path(inner)),
            Rule::sentence => WordArg::Sentence(self.sentence(inner)),
            _ => panic!("invalid word arg"),
        }
    }

    fn identifier(&self, p: Pair<Rule>) -> Identifier {
        assert_eq!(p.as_rule(), Rule::identifier);
        let span = source::Span::from_ast(self.0, p.as_span());
        Identifier(span)
    }

    fn literal(&self, p: Pair<Rule>) -> Literal {
        assert_eq!(p.as_rule(), Rule::literal);
        let inner = p.into_inner().exactly_one().unwrap();
        let span = source::Span::from_ast(self.0, inner.as_span());
        let ty = match inner.as_rule() {
            Rule::int => LiteralType::Int,
            Rule::char_lit => LiteralType::Char,
            Rule::bool => LiteralType::Bool,
            // Rule::symbol => LiteralType::Symbol,
            _ => panic!("invalid literal type"),
        };
        Literal { ty, span }
    }

    fn path(&self, p: Pair<Rule>) -> Path {
        assert_eq!(p.as_rule(), Rule::path);
        let span = source::Span::from_ast(self.0, p.as_span());
        let segments = p.into_inner().map(|p| self.identifier(p)).collect();
        Path { span, segments }
    }
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct File {
    pub mod_path: Vec<source::Span>,
    pub imports: Vec<Identifier>,
    pub namespace: Namespace,
}

#[derive(Debug, Default, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Namespace {
    // pub uses: Vec<Use>,
    pub decls: Vec<Decl>,
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum Decl {
    ConstDecl(ConstDecl),
    SentenceDecl(SentenceDecl),
    ModuleDecl(ModuleDecl),
    // FnDecl(FnDecl),
    // DefDecl(DefDecl),
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct ModuleDecl {
    pub name: Identifier,
    pub namespace: Namespace,
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct ConstDecl {
    pub name: Identifier,
    pub value: ConstExpr,
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum ConstExpr {
    Literal(Literal),
    Path(Path),
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct SentenceDecl {
    pub span: source::Span,
    pub name: Identifier,
    pub sentence: Sentence,
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Sentence {
    pub span: source::Span,
    pub words: Vec<Word>,
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Word {
    pub span: source::Span,
    pub operator: Identifier,
    pub args: Vec<WordArg>,
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub enum WordArg {
    Literal(Literal),
    Path(Path),
    Sentence(Sentence),
}

#[derive(Debug, Clone, Copy, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Literal {
    pub ty: LiteralType,
    pub span: source::Span,
}

impl Literal {
    pub fn into_value(self, sources: &source::Sources) -> bytecode::PrimitiveValue {
        match self.ty {
            LiteralType::Int => {
                bytecode::PrimitiveValue::Usize(self.span.as_str(sources).parse().unwrap())
            }
            LiteralType::Char => {
                bytecode::PrimitiveValue::Char(self.span.as_str(sources).chars().nth(1).unwrap())
            }
            LiteralType::Bool => {
                bytecode::PrimitiveValue::Bool(self.span.as_str(sources).parse().unwrap())
            }
        }
    }
}

#[derive(Debug, Clone, Copy, debug_with::DebugWith)]
#[debug_with(passthrough)]
pub enum LiteralType {
    Int,
    Char,
    Bool,
}

#[derive(Debug, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Path {
    pub span: source::Span,
    pub segments: Vec<Identifier>,
}

#[derive(Debug, Clone, Copy, debug_with::DebugWith)]
#[debug_with(context = source::Sources)]
pub struct Identifier(pub source::Span);

impl<C> crate::compiler2::unresolved::DebugWith<C> for Identifier
where
    source::Span: crate::compiler2::unresolved::DebugWith<C>,
{
    fn debug_with(&self, c: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.debug_with(c, f)
    }
}
