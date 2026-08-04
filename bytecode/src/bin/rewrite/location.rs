//! Where in the tree a rewrite happens.
//!
//! Nothing in the old tool could name a position. Placement was expressed only
//! by composing traversals — `then(once(inline))` meant "the first call in some
//! then arm" — and the position a rule actually fired at survived only as a
//! number in a trace. A script has to say exactly where each step lands, so
//! that applying it is a mechanical check rather than a second search.

// The lower layer lands before anything drives it. Nothing outside the tests
// calls this yet; the engine does once it is generating scripts, and this
// allowance comes off then.
#![allow(dead_code)]

use std::fmt;

use crate::ir::Selector;

/// A window in the tree: how to get to a sequence, and where in it to look.
///
/// The `descent` is read from the root outwards. Each `(index, selector)` step
/// picks the node at `index` in the sequence reached so far and descends into
/// the child body that `selector` names — so `[(3, Then), (0, Body)]` is "the
/// then arm of the node at 3, then the body of the node at 0 within it". `at`
/// is where the window starts in the sequence that walk arrives at.
///
/// **A location addresses the tree as the preceding steps left it.** Locations
/// are not stable across a script: step 5 may name an index that did not exist
/// when step 4 was recorded, and that is not a defect but the whole reason a
/// script is cheaper than a search. What makes it safe is that the applier
/// regenerates the side it expects to find and refuses to splice unless the
/// window matches, so a stale path fails loudly instead of rewriting the wrong
/// code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Location {
    pub(crate) descent: Vec<(usize, Selector)>,
    pub(crate) at: usize,
}

impl Location {
    /// A window in the root sequence.
    pub(crate) fn root(at: usize) -> Self {
        Location {
            descent: Vec::new(),
            at,
        }
    }

    /// This location as seen from `outer`: the descent appended and `at`
    /// shifted by the enclosing window's start.
    ///
    /// A matcher reports where it wants to rewrite *within the window it was
    /// shown*, since it cannot know where in the tree it is being applied. This
    /// is what the driver does with that answer.
    pub(crate) fn under(&self, outer: &[(usize, Selector)], window_start: usize) -> Location {
        let mut descent = outer.to_vec();
        // Only the first leg of the descent is relative to the window; once it
        // has gone down a level the indices are that sequence's own.
        let mut rest = self.descent.iter().copied();
        if let Some((index, sel)) = rest.next() {
            descent.push((window_start + index, sel));
            descent.extend(rest);
            Location {
                descent,
                at: self.at,
            }
        } else {
            Location {
                descent,
                at: window_start + self.at,
            }
        }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.descent.is_empty() {
            let path: Vec<String> = self
                .descent
                .iter()
                .map(|(i, sel)| format!("{}.{}", i, selector_name(*sel)))
                .collect();
            write!(f, "[{}] ", path.join(", "))?;
        }
        write!(f, "@{}", self.at)
    }
}

pub(crate) fn selector_name(sel: Selector) -> &'static str {
    match sel {
        Selector::Then => "then",
        Selector::Else => "else",
        Selector::Body => "body",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_root_window_prints_as_a_bare_offset() {
        assert_eq!(Location::root(5).to_string(), "@5");
    }

    #[test]
    fn a_descent_prints_index_and_kind_outermost_first() {
        let loc = Location {
            descent: vec![(3, Selector::Then), (0, Selector::Body)],
            at: 2,
        };
        assert_eq!(loc.to_string(), "[3.then, 0.body] @2");
    }

    #[test]
    fn a_window_relative_location_at_this_level_shifts_by_the_window_start() {
        // A matcher saying "@1 of the window you showed me" at window start 7.
        let rel = Location::root(1);
        assert_eq!(rel.under(&[], 7), Location::root(8));
    }

    #[test]
    fn a_window_relative_descent_shifts_only_its_first_index() {
        // "the then arm of window node 1, at offset 0" seen from window start 7:
        // the node is at 8, but the offset inside that arm is its own.
        let rel = Location {
            descent: vec![(1, Selector::Then)],
            at: 0,
        };
        assert_eq!(
            rel.under(&[(2, Selector::Body)], 7),
            Location {
                descent: vec![(2, Selector::Body), (8, Selector::Then)],
                at: 0,
            }
        );
    }
}
