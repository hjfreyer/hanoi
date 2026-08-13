//! Stack arities over the term.
//!
//! Mostly structural, but a [`Term::Call`] names a sentence rather than holding
//! its body, so these take a [`Program`] to look the target up. That is the
//! price of making inlining a rule; the gain is that an unexpanded call now has
//! an arity where a cut edge had none.

use bytecode::arity::op_arity;

use crate::ir::Term;
use crate::program::Program;

/// How many values a term takes off the stack and leaves on it, counted from
/// the top. `None` means the reckoning stops there: a call whose target's arity
/// is unknown tells us nothing about what follows.
pub(crate) fn term_arity(prog: &Program, term: &Term) -> Option<(i64, i64)> {
    match term {
        // The whole point of an arity-carrying identity: `par` carves the stack
        // by what its two sides ask for, so the thing that passes `k` values
        // through has to ask for `k`.
        Term::Id(k) => Some((*k as i64, *k as i64)),
        Term::Op(inst) => op_arity(inst),
        Term::Call(target) => prog.arity(*target),
        Term::Compose(a, b) => Some(compose(term_arity(prog, a)?, term_arity(prog, b)?)),
        // Side by side on disjoint parts of one stack: the right runs on the
        // top, the left on what is under it, and neither can see the other's
        // values. So the two demands add, and so do the two results.
        Term::Par { left, right, .. } => {
            let (a, b) = term_arity(prog, left)?;
            let (c, d) = term_arity(prog, right)?;
            Some((a + c, b + d))
        }
        Term::Branch {
            then_body,
            else_body,
            ..
        } => branch_arity(prog, then_body, else_body),
    }
}

/// What running an `(n1 -> m1)` and then an `(n2 -> m2)` takes and leaves.
fn compose((n1, m1): (i64, i64), (n2, m2): (i64, i64)) -> (i64, i64) {
    // Whatever the second wants and the first did not leave has to come from
    // below, and whatever the first left over and the second did not read stays
    // there.
    let short = (n2 - m1).max(0);
    let spare = (m1 - n2).max(0);
    (n1 + short, m2 + spare)
}

/// What a branch takes and leaves, from **both** arms.
///
/// The arity checker holds the two arms to the same *net* change and to
/// nothing else, so they may differ in what they require: `{ }` and
/// `{ drop ; push true }` are both net zero and need nought and one. Reading
/// the arity off whichever arm answered first therefore understated it, and
/// understating an arity is a soundness bug rather than an imprecision —
/// `annihilate` asks only for an arity, so a branch that claimed `(1 -> 0)`
/// when it was really `(2 -> 1)` was rewritten into a `drop` that does not
/// mean the same thing. `--check` could not catch it either, since the two
/// readings have the same net change, which is exactly what it compares.
///
/// So the branch requires what the hungrier arm requires, plus the condition,
/// and leaves what that implies. Both arms agree on the answer because they
/// agree on the net.
///
/// An arm whose own reckoning stops — one holding a call whose arity is not
/// known — answers for neither, and the other arm stands alone. That is the
/// only case in which one arm decides, and it is out of reach of a library that
/// compiled, since inference answers for every sentence in one.
///
/// `None` when neither arm answers, or when the two disagree on net change.
/// Neither is reachable from code the arity checker accepted — but an arity
/// that is not known declines a rewrite, where a wrong one performs it.
fn branch_arity(prog: &Program, then_body: &Term, else_body: &Term) -> Option<(i64, i64)> {
    match (term_arity(prog, then_body), term_arity(prog, else_body)) {
        (Some((tn, tm)), Some((en, em))) => {
            if tm - tn != em - en {
                return None;
            }
            let need = tn.max(en);
            Some((need + 1, need + (tm - tn)))
        }
        (Some((n, m)), None) | (None, Some((n, m))) => Some((n + 1, m)),
        (None, None) => None,
    }
}

/// [`seq_arity`] when the whole run is statically known, which is what a
/// factor's own arity needs — a body that stops partway has no output count.
pub(crate) fn full_arity(prog: &Program, nodes: &[Term]) -> Option<(i64, i64)> {
    let (inputs, outputs) = seq_arity(prog, nodes);
    Some((inputs, outputs?))
}

/// The arity of a run of factors, stopping where the reckoning does.
///
/// Kept alongside [`term_arity`] because a listing wants the entry depth of
/// every factor it prints, including the ones after the first it cannot read.
pub(crate) fn seq_arity(prog: &Program, nodes: &[Term]) -> (i64, Option<i64>) {
    let mut inputs = 0i64;
    let mut size = 0i64;
    for node in nodes {
        let Some((n, m)) = term_arity(prog, node) else {
            return (inputs, None);
        };
        if size < n {
            inputs += n - size;
            size = n;
        }
        size = size - n + m;
    }
    (inputs, Some(size))
}
