use std::collections::{BTreeMap, VecDeque};

use itertools::Itertools;

use crate::{
    flat::{self, SentenceIndex},
    ir,
    source::{self, Span},
};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("At {location}, {name:?} already defined")]
    AlreadyDefined {
        location: source::Location,
        name: Vec<String>,
    }, // #[error("At {location}, unknown reference: {name}")]
       // UnknownReference {
       //     location: source::Location,
       //     name: String,
       // },
}

pub fn compile(sources: &source::Sources, ir: ir::Crate) -> Result<flat::Library, Error> {
    let mut res = flat::Library::default();

    // Build index of sentence names.
    for (sentence_idx, sentence) in ir.sentences.iter_enumerated() {
        let name = sentence
            .name
            .0
            .iter()
            .map(|i| i.0.as_str(sources).to_owned())
            .collect_vec();
        if res
            .sentence_index
            .insert(name.clone(), sentence_idx)
            .is_some()
        {
            return Err(Error::AlreadyDefined {
                location: sentence.span.location(sources).unwrap(),
                name,
            });
        }
    }

    let sentences: Result<Vec<flat::Sentence>, Error> = ir
        .sentences
        .into_iter()
        .map(|s| convert_sentence(sources, &res.sentence_index, s))
        .collect();

    res.sentences = sentences?.into_iter().collect();

    Ok(res)
}

fn convert_sentence(
    sources: &source::Sources,
    sentence_index: &BTreeMap<Vec<String>, SentenceIndex>,
    sentence: ir::Sentence,
) -> Result<flat::Sentence, Error> {
    let mut b = SentenceBuilder::new(sources, sentence_index);

    for word in sentence.words {
        match word {
            ir::Word::Builtin(builtin) => {
                b.ir_builtin(builtin);
            }
            ir::Word::Literal(literal) => b.literal(literal),
        }
    }

    Ok(b.build())
}

pub struct SentenceBuilder<'a> {
    pub sources: &'a source::Sources,
    pub sentence_index: &'a BTreeMap<Vec<String>, SentenceIndex>,
    pub names: VecDeque<Option<String>>,
    pub words: Vec<flat::Word>,
}

impl<'a> SentenceBuilder<'a> {
    pub fn new(
        sources: &'a source::Sources,
        sentence_index: &'a BTreeMap<Vec<String>, SentenceIndex>,
    ) -> Self {
        Self {
            sources,
            sentence_index,
            names: VecDeque::new(),
            words: vec![],
        }
    }

    pub fn build(self) -> flat::Sentence {
        flat::Sentence {
            // name: self.name,
            words: self.words,
        }
    }

    // pub fn literal(&mut self, literal: Literal) {
    //     self.literal_split(literal.span, literal.value)
    // }

    pub fn literal(&mut self, value: ir::Literal) {
        match value {
            ir::Literal::Int(ir::Int { span, value }) => {
                self.push_value(span, flat::Value::Usize(value))
            }
        }
    }

    pub fn push_value(&mut self, span: Span, value: flat::Value) {
        self.words.push(flat::Word {
            inner: flat::InnerWord::Push(value),
            span,
            names: Some(self.names.clone()),
        });
        self.names.push_front(None);
    }

    // pub fn sentence_idx(&mut self, span: Span<'t>, sentence_idx: SentenceIndex) {
    //     self.words.push(Word {
    //         inner: InnerWord::Push(Value::Pointer(Closure(vec![], sentence_idx))),
    //         modname: self.modname.clone(),
    //         span,
    //         names: Some(self.names.clone()),
    //     });
    //     self.names.push_front(None);
    // }

    // pub fn symbol(&mut self, span: Span<'t>, symbol: &str) {
    //     self.literal_split(span, Value::Symbol(symbol.to_owned()))
    // }

    // pub fn mv(&mut self, ident: Identifier<'t>) -> Result<(), BuilderError<'t>> {
    //     let Some(idx) = self.names.iter().position(|n| match n {
    //         Some(n) => n.as_str() == ident.0.as_str(),
    //         None => false,
    //     }) else {
    //         return Err(BuilderError::UnknownReference(ident));
    //     };
    //     Ok(self.mv_idx(ident.0, idx))
    // }

    // pub fn mv_idx(&mut self, span: Span<'t>, idx: usize) {
    //     let names = self.names.clone();
    //     let declared = self.names.remove(idx).unwrap();
    //     self.names.push_front(declared);

    //     self.words.push(Word {
    //         inner: InnerWord::Move(idx),
    //         modname: self.modname.clone(),
    //         span,
    //         names: Some(names),
    //     });
    // }

    // pub fn cp(&mut self, i: Identifier<'t>) -> Result<(), BuilderError<'t>> {
    //     let Some(idx) = self.names.iter().position(|n| match n {
    //         Some(n) => n.as_str() == i.0.as_str(),
    //         None => false,
    //     }) else {
    //         return Err(BuilderError::UnknownReference(i));
    //     };
    //     Ok(self.cp_idx(i.0, idx))
    // }

    // pub fn cp_idx(&mut self, span: Span<'t>, idx: usize) {
    //     let names = self.names.clone();
    //     self.names.push_front(None);

    //     self.words.push(Word {
    //         inner: InnerWord::Copy(idx),
    //         modname: self.modname.clone(),
    //         span,
    //         names: Some(names),
    //     });
    // }

    // pub fn sd_idx(&mut self, span: Span<'t>, idx: usize) {
    //     let names = self.names.clone();

    //     let declared = self.names.pop_front().unwrap();
    //     self.names.insert(idx, declared);

    //     self.words.push(Word {
    //         inner: InnerWord::Send(idx),
    //         modname: self.modname.clone(),
    //         span,
    //         names: Some(names),
    //     });
    // }
    // pub fn sd_top(&mut self, span: Span<'t>) {
    //     self.sd_idx(span, self.names.len() - 1)
    // }

    // pub fn drop_idx(&mut self, span: Span<'t>, idx: usize) {
    //     let names = self.names.clone();
    //     let declared = self.names.remove(idx).unwrap();

    //     self.words.push(Word {
    //         inner: InnerWord::Drop(idx),
    //         modname: self.modname.clone(),
    //         span,
    //         names: Some(names),
    //     });
    // }

    // pub fn path(&mut self, ast::Path { span, segments }: ast::Path<'t>) {
    //     for segment in segments.iter().rev() {
    //         self.literal_split(*segment, Value::Symbol(segment.as_str().to_owned()));
    //     }
    //     self.literal_split(span, Value::Namespace(self.ns_idx));
    //     for segment in segments {
    //         self.builtin(segment, Builtin::Get);
    //     }
    // }

    pub fn ir_builtin(&mut self, builtin: ir::Builtin) {
        let name = builtin.name.0.as_str(self.sources);
        if builtin.args.is_empty() {
            if let Some(b) = flat::Builtin::ALL.iter().find(|b| b.name() == name) {
                self.builtin(builtin.span, *b)
            } else {
                panic!("unknown builtin: {:?}", name)
            }
        } else {
        }
        // match builtin.name.0.as_str(self.sources) {
        //     s =>
        // }
    }

    pub fn builtin(&mut self, span: Span, builtin: flat::Builtin) {
        self.words.push(flat::Word {
            span,
            inner: flat::InnerWord::Builtin(builtin),
            names: Some(self.names.clone()),
        });
        match builtin {
            flat::Builtin::Add
            | flat::Builtin::Eq
            | flat::Builtin::Curry
            | flat::Builtin::Prod
            | flat::Builtin::Lt
            | flat::Builtin::Or
            | flat::Builtin::And
            | flat::Builtin::Sub
            | flat::Builtin::Get
            | flat::Builtin::SymbolCharAt
            | flat::Builtin::Cons => {
                self.names.pop_front();
                self.names.pop_front();
                self.names.push_front(None);
            }
            flat::Builtin::NsEmpty => {
                self.names.push_front(None);
            }
            flat::Builtin::NsGet => {
                let ns = self.names.pop_front().unwrap();
                self.names.pop_front();
                self.names.push_front(ns);
                self.names.push_front(None);
            }
            flat::Builtin::NsInsert | flat::Builtin::If => {
                self.names.pop_front();
                self.names.pop_front();
                self.names.pop_front();
                self.names.push_front(None);
            }
            flat::Builtin::NsRemove => {
                let ns = self.names.pop_front().unwrap();
                self.names.pop_front();
                self.names.push_front(ns);
                self.names.push_front(None);
            }
            flat::Builtin::Not
            | flat::Builtin::SymbolLen
            | flat::Builtin::Deref
            | flat::Builtin::Ord => {
                self.names.pop_front();
                self.names.push_front(None);
            }
            flat::Builtin::AssertEq => {
                self.names.pop_front();
                self.names.pop_front();
            }
            flat::Builtin::Snoc => {
                self.names.pop_front();
                self.names.push_front(None);
                self.names.push_front(None);
            }
        }
    }

    // pub fn tuple(&mut self, span: Span<'t>, size: usize) {
    //     self.words.push(Word {
    //         inner: InnerWord::Tuple(size),
    //         modname: self.modname.clone(),
    //         span: span,
    //         names: Some(self.names.clone()),
    //     });
    //     for _ in 0..size {
    //         self.names.pop_front().unwrap();
    //     }
    //     self.names.push_front(None);
    // }

    // pub fn untuple(&mut self, span: Span<'t>, size: usize) {
    //     self.words.push(Word {
    //         inner: InnerWord::Untuple(size),
    //         modname: self.modname.clone(),
    //         span: span,
    //         names: Some(self.names.clone()),
    //     });
    //     self.names.pop_front();
    //     for _ in 0..size {
    //         self.names.push_front(None);
    //     }
    // }

    // fn func_call(&mut self, call: ast::Call<'t>) -> Result<usize, BuilderError<'t>> {
    //     let argc = call.args.len();

    //     for arg in call.args.into_iter().rev() {
    //         self.value_expr(arg)?;
    //     }

    //     match call.func {
    //         ast::PathOrIdent::Path(p) => self.path(p),
    //         ast::PathOrIdent::Ident(i) => self.mv(i)?,
    //     }
    //     Ok(argc)
    // }

    // fn value_expr(&mut self, expr: ValueExpression<'t>) -> Result<(), BuilderError<'t>> {
    //     match expr {
    //         ValueExpression::Literal(literal) => {
    //             Ok(self.literal_split(literal.span, literal.value))
    //         }
    //         ValueExpression::Path(path) => Ok(self.path(path)),
    //         ValueExpression::Identifier(identifier) => self.mv(identifier),
    //         ValueExpression::Copy(identifier) => self.cp(identifier),
    //         ValueExpression::Closure { span, func, args } => {
    //             let argc = args.len();
    //             for arg in args.into_iter().rev() {
    //                 self.value_expr(arg)?;
    //             }
    //             match func {
    //                 ast::PathOrIdent::Path(p) => self.path(p),
    //                 ast::PathOrIdent::Ident(i) => self.mv(i)?,
    //             }
    //             for _ in 0..argc {
    //                 self.builtin(span, Builtin::Curry);
    //             }
    //             Ok(())
    //         }
    //     }
    // }

    // fn bindings(&mut self, b: Bindings<'t>) {
    //     self.names = b
    //         .bindings
    //         .iter()
    //         .rev()
    //         .map(|b| match b {
    //             ast::Binding::Literal(_) | ast::Binding::Drop(_) => None,
    //             ast::Binding::Ident(span) => Some(span.as_str().to_owned()),
    //         })
    //         .collect();
    //     let mut dropped = 0;
    //     for (idx, binding) in b.bindings.into_iter().rev().enumerate() {
    //         match binding {
    //             ast::Binding::Literal(l) => {
    //                 let span = l.span;
    //                 self.mv_idx(span, idx - dropped);
    //                 self.literal(l);
    //                 self.builtin(span, Builtin::AssertEq);
    //                 dropped += 1;
    //             }
    //             ast::Binding::Drop(span) => {
    //                 self.drop_idx(span, idx - dropped);
    //                 dropped += 1;
    //             }
    //             _ => (),
    //         }
    //     }
    // }
}
