//! The stepper: a derivation, one rule firing at a time.
//!
//! A tactic that does the wrong thing is hard to read backwards from its
//! output. `--trace` says which rules fired and how often, and the listing says
//! where the term ended up, but neither says *when* the term stopped being the
//! one you meant. This walks the derivation: at every step it shows the tree
//! before the last firing beside the tree after it, so what that one rule did
//! is the only thing on the screen, and sketches the window the next rule is
//! about to match.
//!
//! Showing the change rather than the tree is the whole point of the view.
//! A rule firing is a splice of a few nodes; reprinting a thousand-line
//! listing around it is how the first version of this buried what it was
//! supposed to reveal. `list` is there for when the tree itself is the
//! question.
//!
//! **It steps by replaying, not by remembering.** A rule is a pure function of
//! the window it is handed, and the search that places rules reads nothing but
//! the tree, so running the same tactic over the same sentence twice fires the
//! same rules at the same places in the same order. Step *n* is therefore
//! "run it again, with a budget of n firings" — which makes stepping backwards
//! cost exactly what stepping forwards does, and needs no undo log, no
//! snapshots, and not one line of special handling inside the rules.
//!
//! What it costs is re-running the prefix, so walking to step *n* is quadratic
//! in *n*. That is the trade this makes deliberately: a derivation worth
//! reading by hand is tens of firings long, and the alternative buys speed with
//! a second notion of what a rewrite is.

use std::collections::HashSet;
use std::io::{self, BufRead, Write};

use bytecode::SentenceIndex;

use crate::diff::side_by_side;
use crate::ir::{build, Node};
use crate::print::render_body;
use crate::program::Program;
use crate::tactic::{apply, Env, Firing, Tactic};
use crate::Options;

/// Firings listed either side of the cursor by `trace`.
const TRACE_CONTEXT: usize = 8;

pub(crate) fn run(prog: &Program, root: SentenceIndex, tactic: &Tactic, opts: &Options) {
    // One full run, to learn how long the derivation is. It is also where a
    // tactic that will not settle, or a rule that `--check` catches, reports
    // itself — the stepper then walks up to that point and shows the error
    // where it happens, which is the case it is most wanted for.
    let census = Env::stepping(prog, opts.fuel, opts.check, None);
    let ending = match apply(tactic, &census, tree(prog, root)) {
        Ok(_) => None,
        Err(err) => Some(err.to_string()),
    };
    // The log records a firing after it is charged for and applied, so its
    // length is what actually happened — one short of `spent` when the run
    // ended by failing.
    let firings = census.firings();

    let mut session = Session {
        prog,
        root,
        tactic,
        opts,
        at: 0,
        total: firings.len() as u64,
        firings,
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
    tactic: &'a Tactic,
    opts: &'a Options,
    /// Firings applied in the tree currently on screen.
    at: u64,
    /// Firings in the whole derivation.
    total: u64,
    /// Every firing, by name and position. Windows are not sketched here; a
    /// replay that stops at a firing is what renders it.
    firings: Vec<Firing>,
    /// How the full run ended, shown once the cursor reaches the end.
    ending: Option<String>,
    /// Show the whole tree rather than what the last firing changed.
    whole: bool,
    stack: bool,
    /// Repeated by a bare newline, as a debugger should.
    last: String,
}

impl Session<'_> {
    fn repl(&mut self) {
        println!();
        println!(
            "  stepping `{}` — {} rule firing{}.",
            self.opts.tactic,
            self.total,
            if self.total == 1 { "" } else { "s" }
        );
        println!("  Each step shows what one rule firing changed; `list` shows the whole");
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

    /// Shows what the last firing did, and says what the next one will do.
    ///
    /// The diff is the default view because it answers the question stepping
    /// asks. The whole tree is one `list` away, and at step 0 it is all there
    /// is to show.
    fn show(&self) {
        println!();
        match self.at.checked_sub(1).filter(|_| !self.whole) {
            Some(previous) => self.show_diff(previous),
            None => {
                for line in self.lines(self.at) {
                    println!("{}", line);
                }
            }
        }
        self.footer();
    }

    /// The tree either side of the firing that produced the current one.
    fn show_diff(&self, previous: u64) {
        let fired = &self.firings[previous as usize];
        let rows = side_by_side(
            &self.lines(previous),
            &self.lines(self.at),
            &format!("step {}", previous),
            &format!("step {}  ·  {}@{}", self.at, fired.rule, fired.at),
        );
        if rows.is_empty() {
            // No rule returns its window unchanged, so this means the listing
            // cannot show what changed — a provenance label, say.
            println!("  `{}@{}` changed nothing the listing shows.", fired.rule, fired.at);
            return;
        }
        for row in rows {
            println!("{}", row);
        }
    }

    /// Where the cursor is, and what the next firing will do.
    ///
    /// The window is sketched for the firing that has *not* happened yet, which
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
            (true, _) => announce("next", &self.preview()),
            (false, Some(err)) => {
                println!("  next   the run ends here:");
                for line in err.lines() {
                    println!("           {}", line);
                }
            }
            (false, None) => println!("  next   (done — the tactic has nothing left to do)"),
        }
    }

    /// The firing about to happen, with its window.
    ///
    /// A replay that stops one later is what renders it: the derivation is the
    /// same one, so the same rule fires at the same place.
    fn preview(&self) -> Firing {
        self.replay(self.at + 1)
            .1
            .unwrap_or_else(|| self.firings[self.at as usize].clone())
    }

    /// The listing of the tree after `n` firings.
    fn lines(&self, n: u64) -> Vec<String> {
        let body = self.replay(n).0;
        render_body(
            self.prog,
            self.root,
            &body,
            &self.opts.tactic,
            self.stack,
        )
    }

    /// Runs the tactic from scratch, stopping after `n` firings.
    ///
    /// Returns the tree at that point and the firing it stopped at, the only
    /// one whose window this run sketched.
    fn replay(&self, n: u64) -> (Vec<Node>, Option<Firing>) {
        let env = Env::stepping(self.prog, self.opts.fuel, self.opts.check, Some(n));
        match apply(self.tactic, &env, tree(self.prog, self.root)) {
            Ok(outcome) => (outcome.into_nodes(), env.firings().pop()),
            // Unreachable in practice: a run that stops at or before the
            // census's last firing cannot reach whatever ended the census, and
            // `n` never exceeds that. Reported rather than panicked on, since
            // being wrong about that should not lose the session.
            Err(err) => {
                println!("  the replay stopped early: {}", err);
                (Vec::new(), None)
            }
        }
    }

    /// The firing log, windowed around the cursor.
    fn trace(&self) {
        println!();
        if self.firings.is_empty() {
            println!("  no rule fired.");
            return;
        }

        let lo = (self.at as usize).saturating_sub(TRACE_CONTEXT);
        let hi = (self.at as usize + TRACE_CONTEXT).min(self.firings.len());
        if lo > 0 {
            println!("  ... {} earlier", lo);
        }
        if self.at == 0 {
            println!("  ▸        (the cursor is before the first firing)");
        }
        for (i, f) in self.firings[lo..hi].iter().enumerate() {
            let n = lo + i + 1;
            // The cursor sits *after* the firing it last applied.
            let mark = if n as u64 == self.at { "▸" } else { " " };
            println!("  {} {:>4}  {}@{}", mark, n, f.rule, f.at);
        }
        if hi < self.firings.len() {
            println!("  ... {} later", self.firings.len() - hi);
        }

        println!();
        println!("  fired so far");
        let so_far = histogram(&self.firings[..self.at as usize]);
        if so_far.is_empty() {
            println!("  (none)");
        }
        for (rule, count) in so_far {
            println!("  {:<18} {}", rule, count);
        }
    }
}

/// Rule firing counts, most frequent first — the `--trace` table, for a prefix.
fn histogram(firings: &[Firing]) -> Vec<(&'static str, usize)> {
    let mut counts: Vec<(&'static str, usize)> = Vec::new();
    for f in firings {
        match counts.iter_mut().find(|(rule, _)| *rule == f.rule) {
            Some((_, n)) => *n += 1,
            None => counts.push((f.rule, 1)),
        }
    }
    counts.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
    counts
}

fn tree(prog: &Program, root: SentenceIndex) -> Vec<Node> {
    build(prog.library(), root, &mut HashSet::new())
}

/// One firing: which rule, where, and what it does to the window it matches.
///
/// The window goes on its own two lines rather than beside the rule name. A
/// branch with three nodes in each arm is a perfectly ordinary window and does
/// not fit next to anything.
fn announce(label: &str, f: &Firing) {
    println!("  {:<6} {}@{}", label, f.rule, f.at);
    if let Some((before, after)) = &f.detail {
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
        return Err(format!("'{}' takes at most one argument, found '{}'", verb, extra));
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
        other => Err(format!(
            "unknown command '{}'. `help` lists them.",
            other
        )),
    }
}

fn help() {
    println!();
    println!("  s, step [n]   apply n more firings (default 1)");
    println!("  b, back [n]   undo n firings, by replaying that many fewer");
    println!("  g, goto <n>   the tree after exactly n firings");
    println!("  c, continue   run to the end of the derivation");
    println!("  r, restart    back to the tree the tactic starts from");
    println!("  l, list       show the whole tree instead of the change");
    println!("  d, diff       back to showing what the last firing changed");
    println!("  t, trace      the firing log around the cursor, and counts so far");
    println!("  stack         toggle the symbolic stack column (--stack)");
    println!("  h, help       this");
    println!("  q, quit       leave");
    println!();
    println!("  A bare newline repeats the last command, and end of input quits.");
    println!("  A step is one *rule firing*, wherever in the tree it happened; the");
    println!("  `@n` in a firing is a position within its own sequence, not a global");
    println!("  one. The diff is over the listing, so a depth changing counts as a");
    println!("  changed line — which is usually what you want to see.");
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
        let f = |rule| Firing {
            rule,
            at: 0,
            detail: None,
        };
        let log = vec![f("sink"), f("fuse"), f("sink"), f("collapse")];
        assert_eq!(
            histogram(&log),
            vec![("sink", 2), ("collapse", 1), ("fuse", 1)]
        );
        assert_eq!(histogram(&log[..1]), vec![("sink", 1)]);
    }
}
