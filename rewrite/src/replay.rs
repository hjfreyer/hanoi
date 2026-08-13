//! Checking a derivation file against the corpus it is written about.
//!
//! `prove` finds a proof and checks it in one motion: it compiles a tactic,
//! runs the search, and takes what the run left behind. This does the second
//! half alone. It is handed a derivation — the steps, already found, by
//! whatever found them — and answers whether they carry the left-hand side of
//! an identity to its right-hand side.
//!
//! **The point is what is missing.** Nothing here compiles a tactic, places a
//! matcher, or searches for anything; there is no fuel, because a file is
//! finite. What is left is the applier and a parser, which is the whole trusted
//! surface a generator has to be measured against — and a small one, deliberately.
//! A producer in another language emits [`crate::serial`] and this decides,
//! rather than every producer having to be believed.
//!
//! What is checked is exactly what `prove` checks of its own script, in the
//! same code:
//!
//! - both sides may be rewritten at all — neither can fail, which is the
//!   precondition every equation is stated under;
//! - every step applies: the descent reaches a real node, the window is what
//!   the equation regenerates, the side conditions hold against *this* library,
//!   and the replacement leaves the stack as the window did;
//! - what the last step leaves is the right-hand side, compared by effect.
//!
//! A file that arrives with a step whose arguments claim an arity the library
//! does not give is refused at that step, whoever wrote it. Nothing about being
//! written down makes a script trusted; see [`crate::applier`].

use std::collections::HashSet;
use std::path::PathBuf;

use bytecode::{Identity, Library, SentenceIndex};

use crate::applier::apply_script;
use crate::diff::side_by_side;
use crate::ir::{Node, build, same_effect_seq};
use crate::print::render_nodes;
use crate::program::Program;
use crate::prove::{BROKEN, FAILED, OK};
use crate::script::ScriptError;
use crate::serial::{self, Derivation};

pub(crate) struct Options {
    pub(crate) dir: PathBuf,
    pub(crate) files: Vec<PathBuf>,
    pub(crate) check: bool,
    /// Whether every identity the corpus states must be derived here.
    ///
    /// Off, this tool answers about the derivations it was given. On, it also
    /// answers about the ones it was not — which is the question a gate asks,
    /// and a different question from whether what arrived is sound.
    pub(crate) complete: bool,
    pub(crate) stack: bool,
    /// The widest either column of a failure diff may get.
    pub(crate) width: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            dir: PathBuf::new(),
            files: Vec::new(),
            // On by default, as in `prove` and for the same reason: this is a
            // tool whose answer is yes or no, and a wrong yes is worse than a
            // slow run.
            check: true,
            complete: false,
            stack: false,
            width: crate::diff::DEFAULT_WIDTH,
        }
    }
}

/// Checks every derivation in every file, writing its report to `out`.
pub(crate) fn run(opts: &Options, out: &mut dyn std::io::Write) -> std::io::Result<i32> {
    let (_sources, library) = match crate::load(&opts.dir) {
        Ok(pair) => pair,
        Err(err) => {
            write!(out, "{}", err)?;
            if !err.ends_with('\n') {
                writeln!(out)?;
            }
            return Ok(BROKEN);
        }
    };
    let prog = Program::new(&library);

    // Read and parse everything first. A file that will not parse is a broken
    // input rather than a failed claim, and it should not be reported after a
    // page of results from the files that did parse.
    let mut files = Vec::new();
    for path in &opts.files {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(err) => {
                writeln!(out, "error: reading '{}': {}", path.display(), err)?;
                return Ok(BROKEN);
            }
        };
        let parsed = match serial::parse(&source, &prog) {
            Ok(d) => d,
            Err(err) => {
                write!(
                    out,
                    "{}",
                    err.render_in(&source, &path.display().to_string())
                )?;
                return Ok(BROKEN);
            }
        };
        files.push(ParsedFile {
            path: path.clone(),
            source,
            derivations: parsed,
        });
    }

    let total: usize = files.iter().map(|f| f.derivations.len()).sum();
    writeln!(
        out,
        "Checking {}...",
        plural(total, "derivation", "derivations")
    )?;

    let mut passed = 0usize;
    let mut failed = 0usize;
    let mut seen: HashSet<String> = HashSet::new();
    for file in &files {
        for derivation in &file.derivations {
            write!(out, "identity {} ... ", derivation.identity)?;
            match check(&library, &prog, derivation, opts) {
                Ok(name) => {
                    passed += 1;
                    seen.insert(name);
                    writeln!(
                        out,
                        "ok ({})",
                        plural(derivation.steps.len(), "step", "steps")
                    )?;
                }
                Err(failure) => {
                    failed += 1;
                    writeln!(out, "FAILED")?;
                    writeln!(out)?;
                    for line in failure.render(&prog, file, derivation, opts) {
                        writeln!(out, "{}", line)?;
                    }
                    writeln!(out)?;
                }
            }
        }
    }

    // The other question, and it is asked last because it is about the corpus
    // rather than about any one derivation.
    let mut missing = Vec::new();
    if opts.complete {
        for identity in &library.identities {
            if !seen.contains(&identity.name) {
                missing.push(identity.name.clone());
            }
        }
        for name in &missing {
            writeln!(out)?;
            writeln!(out, "error: nothing here derives `{}`", name)?;
            writeln!(
                out,
                "  It is stated in the corpus, and `--complete` asks for every \
                 stated identity."
            )?;
        }
    }

    writeln!(out)?;
    let ok = failed == 0 && missing.is_empty();
    writeln!(
        out,
        "derivation result: {}. {} passed; {} failed{}",
        if ok { "ok" } else { "FAILED" },
        passed,
        failed,
        if opts.complete {
            format!("; {} stated but not derived", missing.len())
        } else {
            String::new()
        }
    )?;
    Ok(if ok { OK } else { FAILED })
}

/// This tool, whole, for a test elsewhere that has just written a derivation
/// file and wants to know whether it checks out.
///
/// `prove`'s tests use it, which is the point: that the two halves agree is a
/// claim about both of them, and it belongs in the one that produces the file.
#[cfg(test)]
pub(crate) fn check_for_tests(dir: &std::path::Path, files: &[PathBuf]) -> (i32, String) {
    let opts = Options {
        dir: dir.to_path_buf(),
        files: files.to_vec(),
        ..Options::default()
    };
    let mut out = Vec::new();
    let code = run(&opts, &mut out).expect("writing to a Vec cannot fail");
    (code, String::from_utf8(out).expect("the report is utf-8"))
}

struct ParsedFile {
    path: PathBuf,
    source: String,
    derivations: Vec<Derivation>,
}

/// Why a derivation did not discharge what it names.
enum Failure {
    /// The corpus states no such identity, or more than one it could be.
    NoSuchIdentity(String),
    /// A step did not fit the tree the steps before it left.
    Step(Box<crate::applier::ApplyError>),
    /// Every step applied, and the last one did not leave the right-hand side.
    NotReached(Vec<Node>, SentenceIndex),
}

/// One derivation, run against the corpus. The name it discharged comes back,
/// since that is what `--complete` counts.
fn check(
    library: &Library,
    prog: &Program,
    derivation: &Derivation,
    opts: &Options,
) -> Result<String, Failure> {
    let index = library
        .identity_by_name(&derivation.identity)
        .map_err(Failure::NoSuchIdentity)?;
    let identity: &Identity = &library.identities[index];

    let mut tree = build_tree(prog, identity.lhs);
    apply_script(prog, &mut tree, &derivation.steps, opts.check)
        .map_err(|e| Failure::Step(Box::new(e)))?;

    // By effect, not by `==`. The two sides were compiled from two sentences,
    // so phase 4 gave every inline block in them a different label, and
    // provenance is not part of a term's identity.
    if same_effect_seq(&tree, &build_tree(prog, identity.rhs)) {
        Ok(identity.name.clone())
    } else {
        Err(Failure::NotReached(tree, identity.rhs))
    }
}

fn build_tree(prog: &Program, root: SentenceIndex) -> Vec<Node> {
    build(prog.library(), root)
}

impl Failure {
    fn render(
        &self,
        prog: &Program,
        file: &ParsedFile,
        derivation: &Derivation,
        opts: &Options,
    ) -> Vec<String> {
        let mut out = Vec::new();
        match self {
            Failure::NoSuchIdentity(why) => {
                out.push("  the corpus states no such identity.".to_string());
                out.push(String::new());
                out.push(format!("  {}", why));
                out.push(String::new());
                out.extend(cite(file, derivation.identity_span));
            }
            Failure::Step(err) => {
                out.push("  a step does not fit.".to_string());
                out.push(String::new());
                for line in err.to_string().lines() {
                    out.push(format!("  {}", line));
                }
                out.push(String::new());
                out.push(
                    "  A location addresses the tree as the steps before it left it,".to_string(),
                );
                out.push(
                    "  so the step that stopped fitting is where the derivation and".to_string(),
                );
                out.push("  the library parted company — not necessarily where the".to_string());
                out.push("  mistake was made.".to_string());
                if let Some(span) = derivation.step_spans.get(err.step) {
                    out.push(String::new());
                    out.extend(cite(file, *span));
                }
            }
            Failure::NotReached(got, rhs) => {
                out.push("  every step applied, and the last one did not leave the".to_string());
                out.push("  right-hand side.".to_string());
                out.push(String::new());
                let want = build_tree(prog, *rhs);
                // Without origins, for the same reason the comparison ignores
                // them: two sides compiled from two sentences share no labels,
                // and none of those differences mean anything.
                let left = render_nodes(prog, got, opts.stack, true, false);
                let right = render_nodes(prog, &want, opts.stack, true, false);
                let rows = side_by_side(
                    &left,
                    &right,
                    "where it landed",
                    "the right-hand side",
                    opts.width,
                );
                if rows.is_empty() {
                    out.push(
                        "  The two listings read alike but are not the same term.".to_string(),
                    );
                    out.extend(left);
                    out.push(String::new());
                    out.extend(right);
                } else {
                    out.extend(rows);
                }
            }
        }
        out
    }
}

/// A span in the file, underlined the way a parse error underlines a word.
///
/// The whole reason a parsed step keeps its span: a derivation with two hundred
/// steps in it is worth nothing to fix if the report only says which number.
///
/// The rendering is a parse error's, with its first line dropped — what has
/// gone wrong is said above, in the words of the layer that noticed, and
/// saying it twice in two voices reads as two problems.
fn cite(file: &ParsedFile, span: (usize, usize)) -> Vec<String> {
    ScriptError::new(String::new(), span)
        .render_in(&file.source, &file.path.display().to_string())
        .lines()
        .skip(1)
        .map(|line| format!("  {}", line))
        .collect()
}

fn plural(n: usize, one: &str, many: &str) -> String {
    if n == 1 {
        format!("{} {}", n, one)
    } else {
        format!("{} {}", n, many)
    }
}

// ---------------------------------------------------------------------------
// The command line
// ---------------------------------------------------------------------------

pub(crate) fn cli() -> i32 {
    let mut opts = Options::default();
    let mut positional: Vec<String> = Vec::new();

    // Indexed rather than a plain iteration, since `--width` takes a value.
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        let mut value = |name: &str| -> Option<String> {
            i += 1;
            match args.get(i) {
                Some(v) => Some(v.clone()),
                None => {
                    eprintln!("{} needs a value", name);
                    None
                }
            }
        };
        match arg {
            "--no-check" => opts.check = false,
            "--complete" => opts.complete = true,
            "--stack" => opts.stack = true,
            "--width" => match value("--width").map(|raw| raw.parse()) {
                Some(Ok(v)) => opts.width = v,
                Some(Err(_)) => {
                    eprintln!("--width needs a number");
                    return BROKEN;
                }
                None => return BROKEN,
            },
            "-h" | "--help" => {
                usage();
                return OK;
            }
            flag if flag.starts_with('-') => {
                eprintln!("Unknown flag: {}", flag);
                usage();
                return BROKEN;
            }
            other => positional.push(other.to_string()),
        }
        i += 1;
    }

    if positional.len() < 2 {
        usage();
        return BROKEN;
    }
    opts.dir = PathBuf::from(&positional[0]);
    opts.files = positional[1..].iter().map(PathBuf::from).collect();

    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    match run(&opts, &mut handle) {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error writing the report: {}", err);
            BROKEN
        }
    }
}

fn usage() {
    eprintln!(
        "Usage: replay <directory> <derivation.{}>... [options]",
        serial::EXTENSION
    );
    eprintln!();
    eprintln!("  Checks each derivation in the given files against the corpus");
    eprintln!("  rooted at <directory>/main.hana: that every step applies, and");
    eprintln!("  that the steps carry the identity's left-hand side to its right.");
    eprintln!();
    eprintln!("  Nothing here searches. The file says which equation to use, with");
    eprintln!("  which arguments, in which direction, at exactly which place, and");
    eprintln!("  this replays it — so anything that can write the format can be");
    eprintln!("  checked by it, whatever language it is written in.");
    eprintln!();
    eprintln!("  --complete           every identity the corpus states must be");
    eprintln!("                       derived by one of these files.");
    eprintln!("  --stack              show what each slot holds, in a failure diff.");
    eprintln!("  --width <n>          how wide each column of a failure diff may get.");
    eprintln!("  --no-check           skip the net-stack-effect check on every step.");
    eprintln!();
    eprintln!("Exit: 0 every derivation checked out, 1 one did not, 2 the input");
    eprintln!("would not load.");
    eprintln!();
    eprintln!("`prove <directory> --emit <file>` writes this format out for every");
    eprintln!("identity it proves, which is where a first example comes from.");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A corpus and a derivation file in a temp directory, since this tool is
    /// about files on disk.
    struct Corpus(PathBuf);

    impl Corpus {
        fn new(name: &str, hana: &str) -> Corpus {
            let dir = std::env::temp_dir().join(format!("hanoi_replay_{}", name));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(dir.join("main.hana"), hana).unwrap();
            Corpus(dir)
        }

        fn with(&self, derivations: &str) -> (i32, String) {
            self.with_opts(derivations, Options::default())
        }

        fn with_opts(&self, derivations: &str, mut opts: Options) -> (i32, String) {
            let path = self.0.join(format!("d.{}", serial::EXTENSION));
            std::fs::write(&path, derivations).unwrap();
            opts.dir = self.0.clone();
            opts.files = vec![path];
            let mut out = Vec::new();
            let code = run(&opts, &mut out).expect("writing to a Vec cannot fail");
            (code, String::from_utf8(out).expect("the report is utf-8"))
        }
    }

    impl Drop for Corpus {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    /// `is_bool ; is_bool` is `bool_result` and then an annihilation.
    const TESTING_A_TEST: &str =
        "identity testing_a_test { is_bool is_bool } = { drop 0 push true };";

    const PROOF: &str = "derivation 1;
proof testing_a_test {
    bool_result(op = is_bool) -> @0;
    annihilate(x = { is_bool }, n = 1, m = 1) -> @0;
}
";

    #[test]
    fn a_derivation_that_lands_on_the_right_hand_side_passes() {
        let c = Corpus::new("pass", TESTING_A_TEST);
        let (code, report) = c.with(PROOF);
        assert_eq!(code, OK, "{}", report);
        assert!(
            report.contains("identity testing_a_test ... ok (2 steps)"),
            "{}",
            report
        );
    }

    /// The failure the whole tool exists to produce: a step that does not fit
    /// the tree the steps before it left.
    #[test]
    fn a_step_that_does_not_fit_says_which_and_where() {
        let c = Corpus::new("misfit", TESTING_A_TEST);
        let (code, report) = c.with(
            "derivation 1;
proof testing_a_test {
    bool_result(op = is_bool) -> @1;
}
",
        );
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("a step does not fit"), "{}", report);
        assert!(report.contains("step 0"), "{}", report);
        // ...and it points at the step in the file rather than counting.
        assert!(report.contains("d.hand:3:5"), "{}", report);
    }

    /// Nothing about being written down makes a step trusted: the arity it
    /// claims is re-derived against the library on every application.
    #[test]
    fn a_step_whose_claimed_arity_is_wrong_is_refused() {
        let c = Corpus::new("arity", TESTING_A_TEST);
        let (code, report) = c.with(
            "derivation 1;
proof testing_a_test {
    bool_result(op = is_bool) -> @0;
    annihilate(x = { is_bool }, n = 2, m = 1) -> @0;
}
",
        );
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("the step claims arity"), "{}", report);
    }

    #[test]
    fn a_derivation_that_stops_short_shows_where_it_landed() {
        let c = Corpus::new("short", TESTING_A_TEST);
        let (code, report) = c.with(
            "derivation 1;
proof testing_a_test {
    bool_result(op = is_bool) -> @0;
}
",
        );
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("did not leave the"), "{}", report);
        assert!(report.contains("the right-hand side"), "{}", report);
    }

    #[test]
    fn a_derivation_of_an_identity_the_corpus_does_not_state_is_refused() {
        let c = Corpus::new("nosuch", TESTING_A_TEST);
        let (code, report) = c.with("derivation 1;\nproof nosuch { }\n");
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("no such identity"), "{}", report);
    }

    #[test]
    fn a_file_that_will_not_parse_is_a_broken_input() {
        let c = Corpus::new("unparsed", TESTING_A_TEST);
        let (code, report) = c.with("derivation 1;\nproof testing_a_test { nonesuch -> @0; }\n");
        assert_eq!(code, BROKEN, "{}", report);
        assert!(report.contains("unknown equation"), "{}", report);
    }

    /// An identity whose two sides are already the same term needs no steps,
    /// and that is a derivation like any other.
    #[test]
    fn an_empty_derivation_proves_a_reflexive_identity() {
        let c = Corpus::new("reflexive", "identity same { drop 0 } = { drop 0 };");
        let (code, report) = c.with("derivation 1;\nproof same { }\n");
        assert_eq!(code, OK, "{}", report);
    }

    /// The gate's question, which is not the same as whether what arrived is
    /// sound.
    #[test]
    fn complete_asks_after_the_identities_no_file_derives() {
        let c = Corpus::new(
            "complete",
            "identity a { drop 0 } = { drop 0 };\nidentity b { drop 0 } = { drop 0 };",
        );
        let (code, report) = c.with_opts(
            "derivation 1;\nproof a { }\n",
            Options {
                complete: true,
                ..Options::default()
            },
        );
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("nothing here derives `b`"), "{}", report);
        // ...and without it, the same file is a clean bill of health.
        let (code, report) = c.with("derivation 1;\nproof a { }\n");
        assert_eq!(code, OK, "{}", report);
    }
}
