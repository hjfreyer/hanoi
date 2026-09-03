//! Phase 2: sugar to core.
//!
//! This pass is purely syntactic and position independent. It needs no module
//! tree and no scope — only a counter for naming anonymous composer modules.
//!
//! # The depth rule
//!
//! Every lowering places its output some number of levels *deeper* than the
//! declaration the user wrote (`type Pair …;` becomes `mod Pair { sentence
//! check }`). Paths are therefore split by who wrote them:
//!
//! * **User-written** paths were written relative to the declaration site, so
//!   they are shifted by the output depth via [`shift_path`].
//! * **Lowerer-generated** paths are emitted relative to the landing site and
//!   need no compensation.
//!
//! The lowerer knows its own output depth by construction, which is why it
//! needs nothing from the module tree. Applying this uniformly is what lets
//! every sentence resolve in the module it is declared in, with no special case
//! for type checks.

use crate::ast::core;
use crate::ast::sugar::{self, Composer};
use crate::ast::{
    IdentityDecl, ParsedInstruction, ParsedSentence, ParsedValue, PrimitiveType, SentenceDecl,
    SourceAnnotation, SymbolDecl, Target, TypeSpec,
};
use crate::library::Annotation;
use crate::resolve::{Path, PathSegment};

/// Lowers a parsed module body into core items.
pub fn lower_items(items: Vec<sugar::Item>) -> Result<Vec<core::Item>, String> {
    Lowerer { anon_counter: 0 }.items(items)
}

/// Rewrites a path written `levels` modules shallower than where it will be
/// resolved. Crate-rooted paths are absolute and need no adjustment.
fn shift_path(path: &Path, levels: usize) -> Path {
    if path.segments.is_empty() || path.segments.first() == Some(&PathSegment::Crate) {
        return path.clone();
    }
    let mut segments = vec![PathSegment::Super; levels];
    segments.extend(path.segments.iter().cloned());
    Path { segments }
}

/// Applies [`shift_path`] to every path a spec mentions. `Literal` holds only
/// bools, ints and const strings, so it has no paths to shift.
fn shift_spec(spec: &TypeSpec, levels: usize) -> TypeSpec {
    match spec {
        TypeSpec::Path(path) => TypeSpec::Path(shift_path(path, levels)),
        TypeSpec::Tuple(elements) => {
            TypeSpec::Tuple(elements.iter().map(|e| shift_spec(e, levels)).collect())
        }
        TypeSpec::Union(variants) => {
            TypeSpec::Union(variants.iter().map(|v| shift_spec(v, levels)).collect())
        }
        TypeSpec::Primitive(_) | TypeSpec::Literal(_) => spec.clone(),
    }
}

fn ident_path(segments: &[&str]) -> Path {
    Path {
        segments: segments
            .iter()
            .map(|s| PathSegment::Identifier(s.to_string()))
            .collect(),
    }
}

fn plain_mod(name: String, items: Vec<core::Item>) -> core::Item {
    core::Item::Mod(core::ModDecl {
        name,
        items,
        is_test: false,
        exports_machine_sentences: false,
    })
}

/// A composer argument, as a path relative to the *declaration* site.
#[derive(Debug, Clone)]
enum ComposerArg {
    Path(Path),
    Value(ParsedValue),
}

impl std::fmt::Display for ComposerArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComposerArg::Path(p) => write!(f, "{}", p),
            ComposerArg::Value(v) => write!(f, "{}", v),
        }
    }
}

struct Lowerer {
    anon_counter: usize,
}

impl Lowerer {
    fn items(&mut self, items: Vec<sugar::Item>) -> Result<Vec<core::Item>, String> {
        let mut lowered = Vec::new();
        for item in items {
            lowered.extend(self.item(item)?);
        }
        Ok(lowered)
    }

    fn item(&mut self, item: sugar::Item) -> Result<Vec<core::Item>, String> {
        match item {
            sugar::Item::Symbol(decl) => Ok(vec![core::Item::Symbol(decl)]),
            sugar::Item::ConstString(decl) => Ok(vec![core::Item::ConstString(decl)]),
            // A sentence is core; the type it may carry is not, and lowers to
            // the identity it states, beside the sentence and at the same
            // depth — so, like an identity's own paths, nothing in it shifts.
            sugar::Item::Sentence(sugar::SentenceDecl { decl, signature }) => {
                let claim = signature
                    .map(|signature| lower_signature(&decl.name, signature))
                    .transpose()?;
                Ok(std::iter::once(core::Item::Sentence(decl))
                    .chain(claim)
                    .collect())
            }
            // Core, so there is nothing to lower. The depth rule does not
            // apply either: an identity emits nothing deeper than where it was
            // written, so no path inside it needs shifting.
            sugar::Item::Identity(decl) => Ok(vec![core::Item::Identity(decl)]),
            sugar::Item::Mod(decl) => Ok(vec![core::Item::Mod(core::ModDecl {
                name: decl.name,
                items: self.items(decl.items)?,
                is_test: decl.is_test,
                exports_machine_sentences: false,
            })]),
            sugar::Item::Type(decl) => Ok(vec![lower_type(decl)?]),
            sugar::Item::Enum(decl) => Ok(vec![lower_enum(decl)?]),
            sugar::Item::Compose(decl) => self.compose(decl),
        }
    }

    /// `mod m compose_X(args);` becomes `mod m { …template items… }`, preceded
    /// by a sibling module for each nested composition.
    fn compose(&mut self, decl: sugar::ComposeDecl) -> Result<Vec<core::Item>, String> {
        let mut siblings = Vec::new();
        let mut args = Vec::new();
        for arg in &decl.args {
            args.push(self.module_expr(arg, &mut siblings)?);
        }

        let generated = self.generate(decl.composer, &args)?;
        siblings.push(core::Item::Mod(core::ModDecl {
            name: decl.name,
            items: generated,
            is_test: decl.is_test,
            // A composed machine's sentences come from a template and carry no
            // `export` markers, so the module has to export them wholesale.
            exports_machine_sentences: decl.is_test,
        }));
        Ok(siblings)
    }

    /// Reduces a composer argument to a path or value. A nested composition is
    /// materialized as an anonymous sibling module and referred to by name.
    fn module_expr(
        &mut self,
        expr: &sugar::ModuleExpr,
        siblings: &mut Vec<core::Item>,
    ) -> Result<ComposerArg, String> {
        match expr {
            sugar::ModuleExpr::Named(path) => Ok(ComposerArg::Path(path.clone())),
            sugar::ModuleExpr::Value(val) => Ok(ComposerArg::Value(val.clone())),
            sugar::ModuleExpr::Composed { composer, args } => {
                let mut lowered = Vec::new();
                for arg in args {
                    lowered.push(self.module_expr(arg, siblings)?);
                }
                let generated = self.generate(*composer, &lowered)?;

                // The name must be a legal identifier: composer templates are
                // rendered as text and re-tokenized, so it round-trips through
                // the lexer.
                let name = format!("__anon_mod_{}", self.anon_counter);
                self.anon_counter += 1;
                siblings.push(plain_mod(name.clone(), generated));

                Ok(ComposerArg::Path(ident_path(&[&name])))
            }
        }
    }

    /// Expands a composer into the items that go inside the composed module.
    ///
    /// Every argument is user-written at the declaration site while the items
    /// land one level deeper, so paths shift by one throughout.
    fn generate(
        &mut self,
        composer: Composer,
        args: &[ComposerArg],
    ) -> Result<Vec<core::Item>, String> {
        let name = composer.name();
        match composer {
            Composer::Concurrent => {
                let paths = expect_paths(args, name, 3)?;
                self.template(
                    TEMPLATE_CONCURRENT,
                    &[("p1", &paths[0]), ("p2", &paths[1]), ("sync_fn", &paths[2])],
                )
            }
            Composer::Hidden => {
                let paths = expect_paths(args, name, 2)?;
                self.template(
                    TEMPLATE_HIDDEN,
                    &[("concurrent", &paths[0]), ("hidden_fn", &paths[1])],
                )
            }
            Composer::Prefix => {
                let paths = expect_paths(args, name, 2)?;
                self.template(
                    TEMPLATE_PREFIX,
                    &[("target", &paths[0]), ("prefix", &paths[1])],
                )
            }
            Composer::RenamePrefix => {
                let paths = expect_paths(args, name, 3)?;
                self.template(
                    TEMPLATE_RENAME_PREFIX,
                    &[
                        ("from_symbol", &paths[0]),
                        ("to_symbol", &paths[1]),
                        ("target", &paths[2]),
                    ],
                )
            }
            Composer::StaticClosure => {
                expect_arity(args, name, 2, "target_machine and a value")?;
                let machine = expect_path(
                    &args[0],
                    name,
                    "first argument must be a machine module path",
                )?;
                let val = as_value(&args[1]);
                self.template(
                    TEMPLATE_STATIC_CLOSURE,
                    &[("machine", &machine), ("val", &val)],
                )
            }
            Composer::Done => {
                if !args.is_empty() {
                    return Err(format!("{} expects 0 arguments", name));
                }
                self.template(TEMPLATE_DONE, &[])
            }
            Composer::Emit => {
                let paths = expect_paths(args, name, 1)?;
                self.template(TEMPLATE_EMIT, &[("machine", &paths[0])])
            }
            Composer::EmitStatic => {
                expect_arity(args, name, 2, "event and target_machine")?;
                let val = as_value(&args[0]);
                let machine = expect_path(
                    &args[1],
                    name,
                    "second argument must be a machine module path",
                )?;
                self.template(
                    TEMPLATE_EMIT_STATIC,
                    &[("machine", &machine), ("val", &val)],
                )
            }
            Composer::Accept => {
                expect_arity(args, name, 2, "value_set and target_machine")?;
                let val_set =
                    expect_path(&args[0], name, "first argument must be a sentence path")?;
                let machine = expect_path(
                    &args[1],
                    name,
                    "second argument must be a machine module path",
                )?;
                self.template(
                    TEMPLATE_ACCEPT,
                    &[("machine", &machine), ("val_set_path", &val_set)],
                )
            }
            Composer::AcceptStatic => {
                expect_arity(args, name, 2, "event and target_machine")?;
                let val = as_value(&args[0]);
                let machine = expect_path(
                    &args[1],
                    name,
                    "second argument must be a machine module path",
                )?;
                self.template(
                    TEMPLATE_ACCEPT_STATIC,
                    &[("machine", &machine), ("val", &val)],
                )
            }
        }
    }

    /// Renders a template and lowers the result.
    ///
    /// Templates are still substituted textually and re-parsed; making them
    /// structured is a separate change. They contain `function` declarations,
    /// which are sugar, so the parsed result has to go back through lowering.
    fn template(
        &mut self,
        template_str: &str,
        vars: &[(&str, &dyn std::fmt::Display)],
    ) -> Result<Vec<core::Item>, String> {
        let mut rendered = template_str.to_string();
        for (name, val) in vars {
            rendered = rendered.replace(&format!("{{{{{}}}}}", name), &val.to_string());
        }

        // The template is generated, so it gets its own map under a name that
        // says so. A failure here is a bug in the template rather than in the
        // user's file, and the rendered error shows the substituted text — the
        // only place the mistake is visible.
        let mut map = crate::source::SourceMap::new();
        let file = map.add("<composer template>", rendered);
        let parsed =
            crate::assembly::parse_source(&mut map, file, None).map_err(|e| map.render(&e))?;
        self.items(parsed)
    }
}

/// Every composer argument is shifted by one: the user wrote it at the
/// declaration site, and the generated items land one module deeper.
const COMPOSER_DEPTH: usize = 1;

fn as_value(arg: &ComposerArg) -> ParsedValue {
    match arg {
        ComposerArg::Value(val) => val.clone(),
        ComposerArg::Path(path) => ParsedValue::Ref(shift_path(path, COMPOSER_DEPTH)),
    }
}

fn expect_path(arg: &ComposerArg, composer: &str, what: &str) -> Result<Path, String> {
    match arg {
        ComposerArg::Path(path) => Ok(shift_path(path, COMPOSER_DEPTH)),
        ComposerArg::Value(_) => Err(format!("{}: {}", composer, what)),
    }
}

fn expect_arity(args: &[ComposerArg], composer: &str, n: usize, what: &str) -> Result<(), String> {
    if args.len() != n {
        return Err(format!(
            "{} expects exactly {} arguments: {}",
            composer, n, what
        ));
    }
    Ok(())
}

fn expect_paths(args: &[ComposerArg], composer: &str, n: usize) -> Result<Vec<Path>, String> {
    if args.len() != n {
        return Err(format!("{} requires exactly {} arguments", composer, n));
    }
    args.iter()
        .map(|arg| match arg {
            ComposerArg::Path(path) => Ok(shift_path(path, COMPOSER_DEPTH)),
            ComposerArg::Value(_) => Err(format!(
                "{} expects path arguments, found a literal value",
                composer
            )),
        })
        .collect()
}

/// The name of the identity `#[type(A -> B)]` on `name` states, which is what
/// a `.hant` proof of the claim addresses it by.
fn signature_identity_name(name: &str) -> String {
    format!("{}_has_type", name)
}

/// `#[type(A -> B)] function f { … }` states, beside `f`,
///
/// ```text
/// identity f_has_type
///     { pick 0 …A… branch { jump f …B… } { drop 0 push true } }
///   = { drop 0 push true };
/// ```
///
/// which is `not (A x) or B (f x)` written the way a branch writes it: either
/// the input was not well-formed, or the output is. The specs compile exactly
/// as a `type` declaration's would, inline rather than as a `check` of their
/// own, and the sentence is reached by the name it was declared under, in the
/// module it was declared in — where the identity lands too, so no path in
/// either spec needs the depth rule applied.
///
/// The identity is a claim and states nothing about how it is proved. In
/// practice the proof beside the file says `inline` and then `by-cases` or
/// `diagram`: a call is opaque to the driver until a proof opens it.
fn lower_signature(name: &str, signature: sugar::Signature) -> Result<core::Item, String> {
    let sugar::Signature {
        input,
        output,
        span,
    } = signature;

    let mut well_formed_output = vec![ParsedInstruction::Jump(Target::Label(ident_path(&[name])))];
    well_formed_output.extend(compile_type_spec(&output)?);

    let constantly_true = || ParsedSentence {
        instructions: vec![
            ParsedInstruction::Drop(0),
            ParsedInstruction::Push(ParsedValue::Bool(true)),
        ],
    };

    let mut lhs = vec![ParsedInstruction::Pick(0)];
    lhs.extend(compile_type_spec(&input)?);
    lhs.push(ParsedInstruction::Branch(
        Target::Inline(ParsedSentence {
            instructions: well_formed_output,
        }),
        Target::Inline(constantly_true()),
    ));

    Ok(core::Item::Identity(IdentityDecl {
        name: signature_identity_name(name),
        lhs: ParsedSentence { instructions: lhs },
        rhs: constantly_true(),
        // Both sides read one value and leave one, and saying so is what
        // makes a sentence that is not `1 -> 1` fail at the claim rather
        // than somewhere inside it.
        annotations: vec![Annotation::Arity(1, 1)],
        span,
    }))
}

/// `type Name spec;` becomes `mod Name { export sentence check { …spec… } }`.
/// The check lands one level below the declaration, so the spec shifts by one.
fn lower_type(decl: sugar::TypeDecl) -> Result<core::Item, String> {
    let spec = shift_spec(&decl.spec, 1);
    let check = check_sentence(&spec, decl.annotations)?;
    Ok(plain_mod(decl.name, vec![core::Item::Sentence(check)]))
}

/// `enum Name { V(specs), … }` becomes a module per variant, each holding a
/// fresh `tag` symbol, a `Body` predicate for the payload, and a `check` for
/// the `(Body, tag)` pair — plus a `check` over the union of variants.
///
/// The tag sits on top of the payload, which is the *last* element of a pair:
/// a value of the variant is `push …body… ; push tag ; tuple 2`.
fn lower_enum(decl: sugar::EnumDecl) -> Result<core::Item, String> {
    let mut items = Vec::new();
    let mut variant_specs = Vec::new();

    for variant in decl.variants {
        // `Body::check` lands three levels below the declaration site
        // (Name / Variant / Body), so the payload specs shift by three.
        let payload = TypeSpec::Tuple(
            variant
                .elements
                .iter()
                .map(|elem| shift_spec(elem, 3))
                .collect(),
        );
        let body_check = check_sentence(&payload, Vec::new())?;

        // `Variant::check` lands in `Name::Variant`, and `tag` and `Body` are
        // its own children, so these generated paths need no prefix.
        let variant_spec = TypeSpec::Tuple(vec![
            TypeSpec::Path(ident_path(&["Body"])),
            TypeSpec::Path(ident_path(&["tag"])),
        ]);
        let variant_check = check_sentence(&variant_spec, Vec::new())?;

        items.push(plain_mod(
            variant.name.clone(),
            vec![
                core::Item::Symbol(SymbolDecl {
                    name: "tag".to_string(),
                }),
                plain_mod("Body".to_string(), vec![core::Item::Sentence(body_check)]),
                core::Item::Sentence(variant_check),
            ],
        ));

        // `Name::check` lands in `Name`, and the variants are its own children.
        variant_specs.push(TypeSpec::Path(ident_path(&[&variant.name])));
    }

    let overall = check_sentence(&TypeSpec::Union(variant_specs), decl.annotations)?;
    items.push(core::Item::Sentence(overall));

    Ok(plain_mod(decl.name, items))
}

/// Builds the exported `check` predicate for a spec.
///
/// A tuple spec asks the shape question with `as_tuple`, which is the coercion
/// `untuple` would apply anyway: the answer on the failing side is a `branch`
/// arm rather than something that stops.
fn check_sentence(
    spec: &TypeSpec,
    annotations: Vec<SourceAnnotation>,
) -> Result<SentenceDecl, String> {
    Ok(SentenceDecl {
        name: "check".to_string(),
        body: ParsedSentence {
            instructions: compile_type_spec(spec)?,
        },
        annotations,
        is_exported: true,
        is_test: false,
    })
}

fn compile_type_spec(spec: &TypeSpec) -> Result<Vec<ParsedInstruction>, String> {
    match spec {
        TypeSpec::Primitive(prim) => Ok(vec![match prim {
            PrimitiveType::Int => ParsedInstruction::IsInt,
            PrimitiveType::Bool => ParsedInstruction::IsBool,
            PrimitiveType::ConstString => ParsedInstruction::IsConstString,
            PrimitiveType::Symbol => ParsedInstruction::IsSymbol,
            PrimitiveType::Tuple => ParsedInstruction::IsTuple(None),
        }]),
        TypeSpec::Literal(val) => Ok(vec![
            ParsedInstruction::Push(val.clone()),
            ParsedInstruction::Equal,
        ]),
        TypeSpec::Path(path) => Ok(vec![ParsedInstruction::TypeCheckPath(path.clone())]),
        TypeSpec::Union(variants) => compile_union(variants),
        TypeSpec::Tuple(elements) => {
            // `is_tuple n` is the whole test. The width is part of the type
            // in exactly the sense `untuple n` means it, so one question asks
            // what the `is_tuple ; tuple_length ; equal` prologue asked in
            // pieces, and what the `pick 0 ; pick 0 ; as_tuple n ; equal`
            // that replaced it asked by coercing a copy and comparing.
            let n = elements.len();
            if n == 0 {
                // At width zero there is nothing left to take apart, so the
                // test is the whole check.
                return Ok(vec![ParsedInstruction::IsTuple(Some(0))]);
            }

            // `untuple n` leaves the last element on top and element 0 in the
            // deepest slot, so the elements are checked back to front: the one
            // this spec names last is the one already under the nose.
            let then_untupled = {
                let mut insts = vec![ParsedInstruction::Untuple(n)];
                insts.extend(compile_type_spec(&elements[n - 1])?);
                for elem in elements.iter().rev().skip(1) {
                    // The result accumulated so far sits on top of the elements
                    // still to check. Hide it rather than rolling it out of the
                    // way, so each element's check runs in a frame that cannot
                    // reach it.
                    insts.push(ParsedInstruction::Dip(
                        1,
                        Target::Inline(ParsedSentence {
                            instructions: compile_type_spec(elem)?,
                        }),
                    ));
                    insts.push(ParsedInstruction::And);
                }
                ParsedSentence {
                    instructions: insts,
                }
            };

            // The value is still whole in this arm, since the test was made on
            // a copy: discard it and answer `false`.
            let else_wrong_shape = ParsedSentence {
                instructions: vec![
                    ParsedInstruction::Drop(0),
                    ParsedInstruction::Push(ParsedValue::Bool(false)),
                ],
            };

            Ok(vec![
                // The test is asked on a copy, so the value survives into
                // both arms: the then arm has it to take apart, and the else
                // arm has it to discard.
                ParsedInstruction::Pick(0),
                ParsedInstruction::IsTuple(Some(n)),
                ParsedInstruction::Branch(
                    Target::Inline(then_untupled),
                    Target::Inline(else_wrong_shape),
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

    let then_true = ParsedSentence {
        instructions: vec![
            ParsedInstruction::Drop(0),
            ParsedInstruction::Push(ParsedValue::Bool(true)),
        ],
    };
    let else_false = ParsedSentence {
        instructions: compile_union(&variants[1..])?,
    };

    let mut insts = vec![ParsedInstruction::Pick(0)];
    insts.extend(compile_type_spec(&variants[0])?);
    insts.push(ParsedInstruction::Branch(
        Target::Inline(then_true),
        Target::Inline(else_false),
    ));

    Ok(insts)
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
