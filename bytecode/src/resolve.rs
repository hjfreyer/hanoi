//! The module tree and name resolution.
//!
//! Constants, sentences, and submodules share a single namespace per module, so
//! a name in a module denotes exactly one [`ModuleItem`]. Modules live in a flat
//! arena and are addressed by [`ModuleId`], and each one knows its parent, so a
//! resolution scope is just an id rather than a path that has to be re-walked
//! from the root.

use std::collections::HashMap;

use derive_more::{From, Into};
use typed_index_collections::TiVec;

use crate::library::SentenceIndex;
use crate::value::Value;

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

/// A type-safe index wrapper for indexing a `Module` in a [`ModuleTree`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From, Into)]
pub struct ModuleId(usize);

/// The crate root, which every [`ModuleTree`] has from the moment it is created.
pub const ROOT: ModuleId = ModuleId(0);

/// A single name binding in a module.
#[derive(Debug, Clone)]
pub enum ModuleItem {
    /// A declared value: a `symbol` or a `const_string`.
    Const(Value),
    Sentence(SentenceIndex),
    Mod(ModuleId),
}

impl ModuleItem {
    /// How to refer to this kind of item in an error message.
    fn describe(&self) -> &'static str {
        match self {
            ModuleItem::Const(Value::Symbol(_)) => "symbol",
            ModuleItem::Const(Value::ConstString(_)) => "const string",
            ModuleItem::Const(_) => "constant",
            ModuleItem::Sentence(_) => "sentence",
            ModuleItem::Mod(_) => "module",
        }
    }
}

/// What a path denotes at a use site. Modules are not items in this sense: a
/// path that names one cannot be pushed or jumped to.
pub enum ResolvedItem {
    Const(Value),
    Sentence(SentenceIndex),
}

impl ResolvedItem {
    /// How to refer to what this is in an error message.
    pub fn describe(&self) -> &'static str {
        match self {
            ResolvedItem::Const(Value::Symbol(_)) => "symbol",
            ResolvedItem::Const(Value::ConstString(_)) => "const string",
            ResolvedItem::Const(_) => "constant",
            ResolvedItem::Sentence(_) => "sentence",
        }
    }
}

struct Module {
    name: String,
    parent: Option<ModuleId>,
    items: HashMap<String, ModuleItem>,
}

pub struct ModuleTree {
    modules: TiVec<ModuleId, Module>,
}

impl Default for ModuleTree {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleTree {
    pub fn new() -> Self {
        Self {
            modules: TiVec::from(vec![Module {
                name: "crate".to_string(),
                parent: None,
                items: HashMap::new(),
            }]),
        }
    }

    pub fn parent(&self, id: ModuleId) -> Option<ModuleId> {
        self.modules[id].parent
    }

    /// The module `up` levels above `id`, or `None` if that walks past the root.
    fn ancestor(&self, id: ModuleId, up: usize) -> Option<ModuleId> {
        let mut cur = id;
        for _ in 0..up {
            cur = self.modules[cur].parent?;
        }
        Some(cur)
    }

    /// The module's path from the crate root, excluding the root itself.
    pub fn path_of(&self, id: ModuleId) -> Vec<String> {
        let mut segments = Vec::new();
        let mut cur = id;
        while let Some(parent) = self.modules[cur].parent {
            segments.push(self.modules[cur].name.clone());
            cur = parent;
        }
        segments.reverse();
        segments
    }

    fn depth(&self, id: ModuleId) -> usize {
        let mut depth = 0;
        let mut cur = id;
        while let Some(parent) = self.modules[cur].parent {
            depth += 1;
            cur = parent;
        }
        depth
    }

    /// The fully qualified name of `name` declared in `scope`, as used to key
    /// the library's flat export/symbol/test maps.
    pub fn fq_name(&self, scope: ModuleId, name: &str) -> String {
        let segments = self.path_of(scope);
        if segments.is_empty() {
            name.to_string()
        } else {
            format!("{}::{}", segments.join("::"), name)
        }
    }

    /// How to refer to a module in an error message.
    fn describe(&self, id: ModuleId) -> String {
        let segments = self.path_of(id);
        if segments.is_empty() {
            "crate".to_string()
        } else {
            format!("crate::{}", segments.join("::"))
        }
    }

    fn check_declarable(&self, scope: ModuleId, name: &str) -> Result<(), String> {
        if name == "crate" || name == "super" {
            return Err(format!("Cannot use reserved keyword '{}' as name", name));
        }
        if let Some(existing) = self.modules[scope].items.get(name) {
            return Err(format!(
                "Duplicate declaration of name '{}' in module '{}': already declared as a {}",
                name,
                self.modules[scope].name,
                existing.describe()
            ));
        }
        Ok(())
    }

    /// Binds `name` in `scope`, rejecting reserved words and redeclarations.
    pub fn declare(
        &mut self,
        scope: ModuleId,
        name: String,
        item: ModuleItem,
    ) -> Result<(), String> {
        self.check_declarable(scope, &name)?;
        self.modules[scope].items.insert(name, item);
        Ok(())
    }

    /// Creates a submodule of `scope` and binds it there.
    pub fn declare_module(&mut self, scope: ModuleId, name: String) -> Result<ModuleId, String> {
        self.check_declarable(scope, &name)?;
        let id = self.modules.next_key();
        self.modules.push(Module {
            name: name.clone(),
            parent: Some(scope),
            items: HashMap::new(),
        });
        self.modules[scope].items.insert(name, ModuleItem::Mod(id));
        Ok(id)
    }

    /// The sentence bound to `name` directly in `scope`, if `name` is one.
    pub fn sentence(&self, scope: ModuleId, name: &str) -> Option<SentenceIndex> {
        match self.modules[scope].items.get(name) {
            Some(ModuleItem::Sentence(idx)) => Some(*idx),
            _ => None,
        }
    }

    /// Every symbol in the tree, keyed by fully qualified name.
    ///
    /// Symbols only: a const string can be written down, so nothing needs to
    /// look one up by the name it was declared under.
    pub fn symbol_map(&self) -> HashMap<String, Value> {
        let mut symbols = HashMap::new();
        for (id, module) in self.modules.iter_enumerated() {
            for (name, item) in &module.items {
                if let ModuleItem::Const(val @ Value::Symbol(_)) = item {
                    symbols.insert(self.fq_name(id, name), val.clone());
                }
            }
        }
        symbols
    }

    /// Resolves `path` as seen from `scope` to the item it denotes.
    pub fn resolve(&self, scope: ModuleId, path: &Path) -> Result<ResolvedItem, String> {
        match self.resolve_entry(scope, path)? {
            ModuleItem::Const(val) => Ok(ResolvedItem::Const(val.clone())),
            ModuleItem::Sentence(idx) => Ok(ResolvedItem::Sentence(*idx)),
            ModuleItem::Mod(_) => Err(format!(
                "Path '{}' names a module, which is not an item",
                path
            )),
        }
    }

    /// Resolves `path` as seen from `scope`, allowing the result to be a module.
    pub fn resolve_entry(&self, scope: ModuleId, path: &Path) -> Result<&ModuleItem, String> {
        let (mut cur, rest) = self.resolve_prefix(scope, &path.segments)?;

        let (last, intermediate) = rest
            .split_last()
            .ok_or_else(|| format!("Path '{}' does not name an item", path))?;

        for seg in intermediate {
            let name = expect_identifier(seg)?;
            cur = match self.modules[cur].items.get(name) {
                Some(ModuleItem::Mod(id)) => *id,
                Some(other) => {
                    return Err(format!(
                        "'{}' in '{}' is a {}, not a module",
                        name,
                        self.describe(cur),
                        other.describe()
                    ));
                }
                None => {
                    return Err(format!(
                        "Module '{}' not found in '{}'",
                        name,
                        self.describe(cur)
                    ));
                }
            };
        }

        let name = expect_identifier(last)?;
        self.modules[cur].items.get(name).ok_or_else(|| {
            format!(
                "Item '{}' not found in module '{}'",
                name,
                self.describe(cur)
            )
        })
    }

    /// Consumes a leading `crate` or run of `super` segments, yielding the
    /// module the rest of the path is relative to.
    fn resolve_prefix<'p>(
        &self,
        scope: ModuleId,
        segments: &'p [PathSegment],
    ) -> Result<(ModuleId, &'p [PathSegment]), String> {
        match segments.first() {
            Some(PathSegment::Crate) => Ok((ROOT, &segments[1..])),
            Some(PathSegment::Super) => {
                let up = segments
                    .iter()
                    .take_while(|seg| matches!(seg, PathSegment::Super))
                    .count();
                let target = self.ancestor(scope, up).ok_or_else(|| {
                    format!(
                        "Path goes up too many levels (current path depth: {})",
                        self.depth(scope)
                    )
                })?;
                Ok((target, &segments[up..]))
            }
            // A bare identifier is relative to the current module; an empty path
            // falls through to the caller's "does not name an item" error.
            _ => Ok((scope, segments)),
        }
    }
}

fn expect_identifier(seg: &PathSegment) -> Result<&str, String> {
    match seg {
        PathSegment::Identifier(name) => Ok(name),
        PathSegment::Crate => Err("'crate' can only appear at the beginning of a path".to_string()),
        PathSegment::Super => Err("'super' can only appear at the beginning of a path".to_string()),
    }
}
