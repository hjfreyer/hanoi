//! The stepper: a derivation, one step at a time.
//!
//! A tactic that does the wrong thing is hard to read backwards from its
//! output. `--trace` says which laws fired and how often, and the listing says
//! where the term ended up, but neither says *when* the term stopped being the
//! one you meant. This walks the derivation: at every step it shows the tree
//! before the last one beside the tree after it, so what that one law did is
//! the only thing on the screen, and sketches the window the next one is about
//! to match.
//!
//! Showing the change rather than the tree is the whole point of the view. A
//! step is a splice of a few nodes; reprinting a thousand-line listing around
//! it is how the first version of this buried what it was supposed to reveal.
//! `list` is there for when the tree itself is the question.
//!
//! **It steps by applying a prefix.** A run produces a script, and a script is
//! a list of steps that can be applied to a fresh tree in order — so the tree
//! after *n* steps is exactly `apply_script(&script[..n])`. Stepping backwards
//! costs what stepping forwards does, and neither needs an undo log or a
//! snapshot.
//!
//! This is what the two-layer split buys the stepper. It used to work by
//! *re-running the search* with a budget of n firings, which was correct only
//! because rules were pure functions of their windows, and which made walking
//! to step *n* quadratic in *n*. Now the derivation is a value; the search runs
//! once.

use std::collections::HashSet;
use std::io::{self, BufRead, Write};

use bytecode::SentenceIndex;

use crate::Options;
use crate::applier::{apply_script, preview};
use crate::diff::side_by_side;
use crate::ir::{Node, build};
use crate::print::render_body;
use crate::program::Program;
use crate::rule::{Script, Step};

/// Steps listed either side of the cursor by `trace`.
const TRACE_CONTEXT: usize = 8;

/// Walks a derivation one step at a time, from the tree `root` builds.
///
/// The search has already happened: what this takes is the script it left
/// behind, which is the only thing a session ever needed. That the derivation
/// might have been assembled by a strategy out of several runs — the backward
/// half of a `normalize`, steps lifted out of a branch arm — makes no difference
/// here, because lifting produced ordinary steps addressed to this same tree.
///
/// `ending` is how the run that produced the script finished, shown once the
/// cursor reaches the end. A tactic that would not settle still recorded
/// everything it did first, so the stepper walks to the failure and shows it
/// where it happens, which is the case it is most wanted for.
pub(crate) fn run(
    prog: &Program,
    root: SentenceIndex,
    script: Script,
    ending: Option<String>,
    opts: &Options,
) {
    let mut session = Session {
        prog,
        root,
        opts,
        at: 0,
        total: script.len() as u64,
        script,
        ending,
        whole: false,
        stack: opts.stack,
        last: "step".to_string(),
    };
    session.repl();
}

struct Session<'a> {
    prog: &'a Program<'a>,
    root: SentenceIndex,
    opts: &'a Options,
    /// Steps applied in the tree currently on screen.
    at: u64,
    /// Steps in the whole derivation.
    total: u64,
    /// The derivation itself. Every view is a prefix of this.
    script: Script,
    /// How the full run ended, shown once the cursor reaches the end.
    ending: Option<String>,
    /// Show the whole tree rather than what the last step changed.
    whole: bool,
    stack: bool,
    /// Repeated by a bare newline, as a debugger should.
    last: String,
}

impl Session<'_> {
    fn repl(&mut self) {
        println!();
        println!(
            "  stepping `{}` — {} step{}.",
            self.opts.tactic,
            self.total,
            if self.total == 1 { "" } else { "s" }
        );
        println!("  Each step shows what one law did; `list` shows the whole");
        println!("  tree, `help` lists the commands, and a bare newline repeats the last.");
        self.show();

        let stdin = io::stdin();
        let mut lines = stdin.lock().lines();
        loop {
            print!("(rewrite {}/{}) ", self.at, self.total);
            let _ = io::stdout().flush();

            // End of input is a quit, so a piped script needs no closing `q`.
            let Some(Ok(line)) = lines.next() else {
                println!();
                return;
            };
            // A blank line leaves `last` alone, which is what makes it repeat.
            if !line.trim().is_empty() {
                self.last = line;
            }

            match parse(&self.last) {
                Ok(Command::Quit) => return,
                Ok(cmd) => self.run_command(cmd),
                Err(msg) => println!("  {}", msg),
            }
        }
    }

    fn run_command(&mut self, cmd: Command) {
        match cmd {
            Command::Step(n) => self.goto(self.at.saturating_add(n)),
            Command::Back(n) => self.goto(self.at.saturating_sub(n)),
            Command::Goto(n) => self.goto(n),
            Command::End => self.goto(self.total),
            Command::Start => self.goto(0),
            Command::List => {
                self.whole = true;
                self.show();
            }
            Command::Diff => {
                self.whole = false;
                self.show();
            }
            Command::Trace => self.trace(),
            Command::Stack => {
                self.stack = !self.stack;
                self.show();
            }
            Command::Help => help(),
            // Handled by the caller, which has to stop reading rather than
            // print something.
            Command::Quit => unreachable!("quit ends the loop"),
        }
    }

    /// Moves the cursor and shows the tree there.
    ///
    /// A move that lands where the cursor already is says so instead of
    /// printing the same tree again: at the end of a long derivation, pressing
    /// `s` once too often should not scroll the listing off the screen. `list`
    /// is how you ask for the tree again on purpose.
    fn goto(&mut self, n: u64) {
        let want = n.min(self.total);
        if want == self.at {
            println!("  already there — step {} of {}.", self.at, self.total);
            return;
        }
        self.at = want;
        self.show();
    }

    /// Shows what the last step did, and says what the next one will do.
    ///
    /// The diff is the default view because it answers the question stepping
    /// asks. The whole tree is one `list` away, and at step 0 it is all there
    /// is to show.
    fn show(&self) {
        println!();
        match self.at.checked_sub(1).filter(|_| !self.whole) {
            Some(previous) => self.show_diff(previous),
            None => {
                for line in self.lines(self.at, true) {
                    println!("{}", line);
                }
            }
        }
        self.footer();
    }

    /// The tree either side of the step that produced the current one.
    ///
    /// Without the position column: a splice renumbers every sibling after it,
    /// so a step that shortened a sequence would report the whole rest of that
    /// sequence as changed. `list` is the view that numbers the nodes, since
    /// aiming is what the numbers are for and the whole tree is where you aim.
    fn show_diff(&self, previous: u64) {
        let taken = &self.script[previous as usize];
        let rows = side_by_side(
            &self.lines(previous, false),
            &self.lines(self.at, false),
            &format!("step {}", previous),
            &format!("step {}  ·  {}", self.at, taken),
            self.opts.width,
        );
        if rows.is_empty() {
            // No equation returns its window unchanged, so this means the
            // listing cannot show what changed — a provenance label, say.
            println!("  `{}` changed nothing the listing shows.", taken);
            return;
        }
        for row in rows {
            println!("{}", row);
        }
    }

    /// Where the cursor is, and what the next step will do.
    ///
    /// The window is sketched for the step that has *not* happened yet, which
    /// is the one the diff above cannot show.
    fn footer(&self) {
        println!();
        println!(
            "  step {} of {}{}",
            self.at,
            self.total,
            if self.whole { "   (whole tree)" } else { "" }
        );
        match (self.at < self.total, &self.ending) {
            (true, _) => announce("next", self.prog, self.next_step()),
            (false, Some(err)) => {
                println!("  next   the run ends here:");
                for line in err.lines() {
                    println!("           {}", line);
                }
            }
            (false, None) => println!("  next   (done — the tactic has nothing left to do)"),
        }
    }

    /// The step about to be taken.
    ///
    /// It is simply the next entry in the script — no second run and nothing to
    /// reconstruct, since the derivation is a value the session already holds.
    fn next_step(&self) -> &Step {
        &self.script[self.at as usize]
    }

    /// The listing of the tree after `n` steps.
    fn lines(&self, n: u64, positions: bool) -> Vec<String> {
        let body = self.tree_at(n);
        render_body(
            self.prog,
            self.root,
            &body,
            &self.opts.tactic,
            self.stack,
            positions,
        )
    }

    /// The tree a prefix of the script produces.
    ///
    /// Applying `n` steps to a fresh build, which is all "the tree after n
    /// steps" has ever meant. A step that will not apply is reported rather
    /// than panicked on: the session is worth keeping even when the script it
    /// is walking has stopped fitting.
    fn tree_at(&self, n: u64) -> Vec<Node> {
        let mut body = tree(self.prog, self.root);
        let prefix = &self.script[..(n as usize).min(self.script.len())];
        if let Err(err) = apply_script(self.prog, &mut body, prefix, self.opts.check) {
            println!("  the derivation stopped fitting: {}", err);
        }
        body
    }

    /// The firing log, windowed around the cursor.
    fn trace(&self) {
        println!();
        if self.script.is_empty() {
            println!("  nothing fired.");
            return;
        }

        let lo = (self.at as usize).saturating_sub(TRACE_CONTEXT);
        let hi = (self.at as usize + TRACE_CONTEXT).min(self.script.len());
        if lo > 0 {
            println!("  ... {} earlier", lo);
        }
        if self.at == 0 {
            println!("  ▸        (the cursor is before the first step)");
        }
        for (i, s) in self.script[lo..hi].iter().enumerate() {
            let n = lo + i + 1;
            // The cursor sits *after* the step it last applied.
            let mark = if n as u64 == self.at { "▸" } else { " " };
            println!("  {} {:>4}  {}", mark, n, s);
        }
        if hi < self.script.len() {
            println!("  ... {} later", self.script.len() - hi);
        }

        println!();
        println!("  fired so far");
        let so_far = histogram(&self.script[..self.at as usize]);
        if so_far.is_empty() {
            println!("  (none)");
        }
        for (rule, count) in so_far {
            println!("  {:<18} {}", rule, count);
        }
    }
}

/// Rule counts, most frequent first — the `--trace` table, for a prefix.
fn histogram(steps: &[Step]) -> Vec<(&'static str, usize)> {
    let mut counts: Vec<(&'static str, usize)> = Vec::new();
    for step in steps {
        let name = step.kind.name();
        match counts.iter_mut().find(|(rule, _)| *rule == name) {
            Some((_, n)) => *n += 1,
            None => counts.push((name, 1)),
        }
    }
    counts.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
    counts
}

fn tree(prog: &Program, root: SentenceIndex) -> Vec<Node> {
    build(prog.library(), root, &mut HashSet::new())
}

/// One step: which law, which way, where, and what it does to its window.
///
/// The window goes on its own two lines rather than beside the name. A branch
/// with three nodes in each arm is a perfectly ordinary window and does not fit
/// next to anything.
fn announce(label: &str, prog: &Program, step: &Step) {
    println!("  {:<6} {}", label, step);
    if let Some((before, after)) = preview(prog, step) {
        println!("           {}", before);
        println!("        ⇒  {}", after);
    }
}

#[derive(Debug, PartialEq)]
enum Command {
    Step(u64),
    Back(u64),
    Goto(u64),
    End,
    Start,
    List,
    Diff,
    Trace,
    Stack,
    Help,
    Quit,
}

/// Parses one command line, or says what is wrong with it.
///
/// One word and at most one argument: this is a stepper, not a shell, and an
/// unknown word is worth an error rather than a guess.
fn parse(line: &str) -> Result<Command, String> {
    let mut words = line.split_whitespace();
    let Some(verb) = words.next() else {
        return Ok(Command::Step(1));
    };
    let arg = words.next();
    if let Some(extra) = words.next() {
        return Err(format!(
            "'{}' takes at most one argument, found '{}'",
            verb, extra
        ));
    }

    let count = |default: u64| -> Result<u64, String> {
        match arg {
            None => Ok(default),
            Some(word) => word
                .parse()
                .map_err(|_| format!("'{}' is not a number of steps", word)),
        }
    };

    match verb {
        "s" | "step" => Ok(Command::Step(count(1)?)),
        "b" | "back" => Ok(Command::Back(count(1)?)),
        "g" | "goto" => match arg {
            Some(_) => Ok(Command::Goto(count(0)?)),
            None => Err("`goto` needs a step number; `restart` and `end` are the two ends".into()),
        },
        "c" | "continue" | "end" => Ok(Command::End),
        "r" | "restart" => Ok(Command::Start),
        "l" | "list" => Ok(Command::List),
        "d" | "diff" => Ok(Command::Diff),
        "t" | "trace" => Ok(Command::Trace),
        "stack" => Ok(Command::Stack),
        "h" | "help" | "?" => Ok(Command::Help),
        "q" | "quit" => Ok(Command::Quit),
        other => Err(format!("unknown command '{}'. `help` lists them.", other)),
    }
}

fn help() {
    println!();
    println!("  s, step [n]   apply n more steps (default 1)");
    println!("  b, back [n]   undo n steps, by applying that many fewer");
    println!("  g, goto <n>   the tree after exactly n steps");
    println!("  c, continue   run to the end of the derivation");
    println!("  r, restart    back to the tree the tactic starts from");
    println!("  l, list       show the whole tree, with the position of each node");
    println!("  d, diff       back to showing what the last firing changed");
    println!("  t, trace      the derivation around the cursor, and counts so far");
    println!("  stack         toggle the symbolic stack column (--stack)");
    println!("  h, help       this");
    println!("  q, quit       leave");
    println!();
    println!("  A bare newline repeats the last command, and end of input quits.");
    println!("  A step is one use of one law, in one direction, at one place. A");
    println!("  matcher may take several: `factor` is three. The location reads");
    println!("  outermost-first, so `[0.else] @2` is the third node of the else arm");
    println!("  of the first. The diff is over the listing, so a depth changing");
    println!("  counts as a changed line — which is usually what you want to see.");
    println!("  The diff leaves the `pos` column out, because a splice renumbers");
    println!("  every sibling after it; `list` is where the positions are.");
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cmd(line: &str) -> Command {
        parse(line).unwrap_or_else(|e| panic!("`{}` did not parse: {}", line, e))
    }

    #[test]
    fn a_bare_newline_is_a_single_step() {
        assert_eq!(cmd(""), Command::Step(1));
        assert_eq!(cmd("   "), Command::Step(1));
    }

    #[test]
    fn counts_default_to_one_and_are_read_when_given() {
        assert_eq!(cmd("s"), Command::Step(1));
        assert_eq!(cmd("step 12"), Command::Step(12));
        assert_eq!(cmd("b"), Command::Back(1));
        assert_eq!(cmd("back 3"), Command::Back(3));
    }

    #[test]
    fn goto_insists_on_a_destination() {
        assert_eq!(cmd("goto 7"), Command::Goto(7));
        assert!(parse("goto").unwrap_err().contains("needs a step number"));
    }

    #[test]
    fn a_mistyped_count_says_so_rather_than_stepping_once() {
        // The failure worth avoiding: `step forward` silently doing one step,
        // which looks like the command was understood.
        assert!(parse("step forward").unwrap_err().contains("not a number"));
        assert!(parse("s 1 2").unwrap_err().contains("at most one argument"));
    }

    #[test]
    fn an_unknown_command_points_at_help() {
        let msg = parse("frobnicate").unwrap_err();
        assert!(msg.contains("unknown command"), "{}", msg);
        assert!(msg.contains("help"), "{}", msg);
    }

    #[test]
    fn the_histogram_counts_a_prefix_most_frequent_first() {
        use crate::location::Location;
        use crate::rule::{Direction, Rule, StepKind};

        let step = |rule: Rule| Step {
            kind: StepKind::Rule(rule),
            dir: Direction::Forward,
            loc: Location::root(0),
        };
        let collapse = || {
            step(Rule::Collapse {
                k: 1,
                j: 1,
                a: Vec::new(),
                outer: Vec::new(),
                inner: Vec::new(),
            })
        };
        let fuse = || {
            step(Rule::Fuse {
                k: 1,
                a: Vec::new(),
                b: Vec::new(),
                a_origins: Vec::new(),
                b_origins: Vec::new(),
            })
        };
        let cancel = || step(Rule::CancelTuple { n: 2 });

        let log = vec![cancel(), fuse(), cancel(), collapse()];
        assert_eq!(
            histogram(&log),
            vec![("cancel_tuple", 2), ("collapse", 1), ("fuse", 1)]
        );
        assert_eq!(histogram(&log[..1]), vec![("cancel_tuple", 1)]);
    }
}
