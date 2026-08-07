//! Checking that every identity a corpus states has a proof that discharges it.
//!
//! `.hana` states the claim, the sibling `.hant` proves it, and this walks the
//! two together. What it is for is that a claim should be worth something:
//! `rewrite` can show two programs are interchangeable, but the showing was
//! printed and lost, so nothing re-checked it when the library changed
//! underneath.
//!
//! **A proof is one-sided.** The tactic rewrites the left-hand side; the result
//! must be the right-hand side. Every step is an equation, so what the run
//! leaves behind is a derivation LHS ⇒ RHS — one linear script, which is a
//! thing that can be replayed, printed, stepped through and diffed. The cost is
//! that the right-hand side has to be written in the form the tactic lands on;
//! see `docs/identities.md`.
//!
//! Two things here deliberately differ from `rewrite`, and both are the same
//! difference: `rewrite` explores, and this decides.
//!
//! - **A miss fails a proof**, where in `rewrite` it is a diagnostic that still
//!   prints the tree. `at(9, sink)` in a proof is a claim that there is
//!   something at 9; when there is not, the proof is written against a tree it
//!   no longer describes, even if the goal was reached anyway.
//! - **`--check` is on by default.** In `rewrite` it is opt-in because the
//!   listing is the answer and the check only costs time. Here the answer is
//!   *yes* or *no*, and a wrong yes is worse than a slow run.

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use bytecode::{Identity, IdentityIndex, Library, SentenceIndex, SourceMap};

use crate::applier::apply_script;
use crate::diff::side_by_side;
use crate::engine::{Env, Tactic, TacticError, miss_report, run as run_tactic};
use crate::ir::{Node, build, same_effect_seq};
use crate::print::render_nodes;
use crate::program::Program;
use crate::rule::Script;
use crate::script::{Definitions, PRELUDE, ProofFile, ScriptError};
use crate::{DEFAULT_FUEL, Precondition, check_preconditions, precondition_explanation};

pub(crate) struct Options {
    pub(crate) dir: PathBuf,
    pub(crate) filter: Option<String>,
    pub(crate) fuel: u64,
    pub(crate) check: bool,
    pub(crate) show_script: bool,
    pub(crate) stack: bool,
    pub(crate) tactic_files: Vec<PathBuf>,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            dir: PathBuf::new(),
            filter: None,
            fuel: DEFAULT_FUEL,
            // On by default, where `rewrite` has it opt-in. This is the tool
            // whose job is to be sure.
            check: true,
            show_script: false,
            stack: false,
            tactic_files: Vec::new(),
        }
    }
}

/// `prove` distinguishes "a claim is wrong" from "the tree will not build",
/// because in CI those want different reactions.
pub(crate) const OK: i32 = 0;
pub(crate) const FAILED: i32 = 1;
pub(crate) const BROKEN: i32 = 2;

/// Checks every identity in the corpus, writing its report to `out`.
///
/// Writing to a `Write` rather than to stdout is what makes this testable
/// without a subprocess — every failure mode below has a test that reads the
/// report back.
pub(crate) fn run(opts: &Options, out: &mut dyn std::io::Write) -> std::io::Result<i32> {
    let (sources, library) = match crate::load(&opts.dir) {
        Ok(pair) => pair,
        Err(err) => {
            write!(out, "{}", err)?;
            if !err.ends_with('\n') {
                writeln!(out)?;
            }
            return Ok(BROKEN);
        }
    };

    let mut base = Definitions::new();
    base.load(PRELUDE)
        .expect("the built-in prelude parses; if it does not, that is a bug");
    for path in &opts.tactic_files {
        let source = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(err) => {
                writeln!(out, "error: reading '{}': {}", path.display(), err)?;
                return Ok(BROKEN);
            }
        };
        if let Err(err) = base.load(&source) {
            write!(
                out,
                "{}",
                err.render_in(&source, &path.display().to_string())
            )?;
            return Ok(BROKEN);
        }
    }

    let prog = Program::new(&library);
    let files = match collect(&opts.dir, &sources, &library, &prog, &base) {
        Ok(files) => files,
        Err(problems) => {
            // All of them, not the first. A tree missing three `.hant` files
            // should say so once rather than over three runs.
            for problem in &problems {
                writeln!(out, "{}", problem)?;
            }
            return Ok(FAILED);
        }
    };

    check_all(&library, &prog, &files, opts, out)
}

// ---------------------------------------------------------------------------
// Discovery
// ---------------------------------------------------------------------------

/// One `.hant`, parsed, with each of its proofs paired to what it proves.
struct ProvenFile {
    hant: PathBuf,
    source: String,
    file: ProofFile,
    /// `(identity, index into file.proofs)`, in the order the identities were
    /// stated.
    pairs: Vec<(IdentityIndex, usize)>,
}

/// Pairs every stated identity with its proof, or says everything that is wrong.
///
/// The rule is one `.hant` beside each `.hana`, checked as a bijection in both
/// directions. It governs where a proof *lives*, not what it may reference — so
/// the day a proof may cite an identity stated elsewhere, nothing here changes.
fn collect(
    dir: &Path,
    sources: &SourceMap,
    library: &Library,
    prog: &Program,
    base: &Definitions,
) -> Result<Vec<ProvenFile>, Vec<String>> {
    let mut out = Vec::new();
    let mut problems = Vec::new();
    let mut expected: HashSet<PathBuf> = HashSet::new();

    // The files that state something, in the order the assembler read them, so
    // the report is deterministic.
    let mut files = Vec::new();
    for identity in &library.identities {
        if !files.contains(&identity.span.file) {
            files.push(identity.span.file);
        }
    }

    for file in files {
        let stated = library.identities_in(file);
        let Some(hana) = sources.path(file) else {
            problems.push(format!(
                "error: '{}' states an identity but is not a file on disk\n  \
                 An identity is proved in the file beside the one that states it, \
                 and there is no beside here.",
                sources.name(file)
            ));
            continue;
        };
        let hant = hana.with_extension("hant");
        expected.insert(hant.clone());

        let Ok(source) = std::fs::read_to_string(&hant) else {
            problems.push(missing_hant(library, &stated, hana, &hant));
            continue;
        };

        let parsed = match ProofFile::parse(&source, base, prog) {
            Ok(f) => f,
            Err(err) => {
                problems.push(err.render_in(&source, &hant.display().to_string()));
                continue;
            }
        };

        // Every proof names an identity stated in this file...
        let mut proved: Vec<Option<usize>> = vec![None; stated.len()];
        for (i, proof) in parsed.proofs.iter().enumerate() {
            match resolve_here(library, &stated, &proof.path) {
                Ok(pos) => proved[pos] = Some(i),
                Err(why) => problems.push(
                    ScriptError::about(
                        format!("no identity `{}` to prove here", proof.path),
                        proof.path_span,
                        why,
                    )
                    .render_in(&source, &hant.display().to_string()),
                ),
            }
        }
        // ...and every identity stated here has one.
        let mut pairs = Vec::new();
        for (pos, slot) in proved.iter().enumerate() {
            match slot {
                Some(i) => pairs.push((stated[pos], *i)),
                None => problems.push(format!(
                    "error: '{}' has no proof of `{}`\n  \
                     It is stated in '{}'; write `proof {} = <tactic>;`",
                    hant.display(),
                    library.identities[stated[pos]].name,
                    hana.display(),
                    short(&library.identities[stated[pos]].name)
                )),
            }
        }

        out.push(ProvenFile {
            hant,
            source,
            file: parsed,
            pairs,
        });
    }

    // A `.hant` beside a `.hana` that states nothing, or beside no `.hana` at
    // all, is invisible to the walk above — which is exactly the case worth
    // catching, since renaming a `.hana` orphans its proofs silently.
    for stray in hant_files(dir) {
        if !expected.contains(&stray) {
            problems.push(format!(
                "error: '{}' proves nothing\n  \
                 No identity is stated in '{}'. A `.hant` is read as the sibling of a \
                 `.hana` that states one; pass it to `--tactics` if it holds tactic \
                 definitions only.",
                stray.display(),
                stray.with_extension("hana").display()
            ));
        }
    }

    if problems.is_empty() {
        Ok(out)
    } else {
        Err(problems)
    }
}

fn missing_hant(library: &Library, stated: &[IdentityIndex], hana: &Path, hant: &Path) -> String {
    let wanted: Vec<String> = stated
        .iter()
        .map(|i| {
            format!(
                "    proof {} = <tactic>;",
                short(&library.identities[*i].name)
            )
        })
        .collect();
    format!(
        "error: '{}' has no proofs\n  \
         '{}' states {}, and an identity is proved in the `.hant` beside the `.hana` \
         that states it.\n  Write:\n\n{}",
        hant.display(),
        hana.display(),
        plural(stated.len(), "identity", "identities"),
        wanted.join("\n")
    )
}

/// Every `.hant` under `dir`, recursively — `tests/advent/` holds `.hana` files
/// too, so a flat listing would miss a `.hant` beside one.
fn hant_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(at) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "hant") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

/// Which of this file's identities a proof names.
///
/// Resolution is suffix matching over the identities *stated in this file*,
/// rather than module-relative resolution: a `.hant` is not part of the module
/// tree — its sibling's own module path is decided by whoever wrote
/// `mod identities;` — so it has no scope of its own, and this is the reading a
/// sentence and a symbol already get.
fn resolve_here(library: &Library, stated: &[IdentityIndex], path: &str) -> Result<usize, String> {
    let suffix = format!("::{}", path);
    let matches: Vec<usize> = stated
        .iter()
        .enumerate()
        .filter(|(_, i)| {
            let name = &library.identities[**i].name;
            name == path || name.ends_with(&suffix)
        })
        .map(|(pos, _)| pos)
        .collect();
    match matches[..] {
        [only] => Ok(only),
        _ if matches.len() > 1 => Err("it is ambiguous here; write more of the path".to_string()),
        // It may exist somewhere else, and saying where is the whole content of
        // the mistake.
        _ => Err(match library.identity_by_name(path) {
            Ok(other) => format!(
                "`{}` is stated in another file, and an identity is proved beside \
                 where it is stated",
                library.identities[other].name
            ),
            Err(_) => {
                let names: Vec<&str> = stated
                    .iter()
                    .map(|i| library.identities[*i].name.as_str())
                    .collect();
                format!("this file states: {}", names.join(", "))
            }
        }),
    }
}

// ---------------------------------------------------------------------------
// Checking
// ---------------------------------------------------------------------------

fn check_all(
    library: &Library,
    prog: &Program,
    files: &[ProvenFile],
    opts: &Options,
    out: &mut dyn std::io::Write,
) -> std::io::Result<i32> {
    let mut selected = Vec::new();
    let mut filtered = 0usize;
    for file in files {
        for (identity, proof) in &file.pairs {
            let wanted = match &opts.filter {
                Some(sub) => library.identities[*identity].name.contains(sub),
                None => true,
            };
            if wanted {
                selected.push((file, *identity, *proof));
            } else {
                filtered += 1;
            }
        }
    }

    writeln!(
        out,
        "Proving {}...",
        plural(selected.len(), "identity", "identities")
    )?;

    let mut passed = 0usize;
    let mut failed = 0usize;
    for (file, index, proof) in &selected {
        let identity = &library.identities[*index];
        write!(out, "identity {} ... ", identity.name)?;
        match check(prog, identity, file, *proof, opts) {
            Ok(script) => {
                passed += 1;
                writeln!(out, "ok ({})", plural(script.len(), "step", "steps"))?;
                if opts.show_script {
                    writeln!(out)?;
                    for line in crate::derivation_lines(prog, &script) {
                        writeln!(out, "{}", line)?;
                    }
                    writeln!(out)?;
                }
            }
            Err(failure) => {
                failed += 1;
                writeln!(out, "FAILED")?;
                writeln!(out)?;
                for line in failure.render(prog, identity, file, *proof, opts) {
                    writeln!(out, "{}", line)?;
                }
                writeln!(out)?;
            }
        }
    }

    writeln!(out)?;
    writeln!(
        out,
        "identity result: {}. {} passed; {} failed; {} filtered out",
        if failed == 0 { "ok" } else { "FAILED" },
        passed,
        failed,
        filtered
    )?;
    Ok(if failed == 0 { OK } else { FAILED })
}

/// Why an identity did not come out proved.
enum Failure {
    /// A side the equations cannot speak about at all.
    Side(Precondition, &'static str, String),
    /// The proof expression does not resolve.
    Proof(String),
    /// The tactic ran out of fuel, was refused, or failed.
    Ran(TacticError),
    /// An aimed step matched nothing.
    Missed(Vec<String>),
    /// It ran, and landed somewhere else.
    NotReached(Vec<Node>),
    /// The script does not reproduce the run. A bug here, not in the proof.
    Replay(String),
}

/// Runs one proof, returning its derivation.
fn check(
    prog: &Program,
    identity: &Identity,
    file: &ProvenFile,
    proof: usize,
    opts: &Options,
) -> Result<Script, Failure> {
    // Both sides, not only the one that gets rewritten: the right-hand side is
    // the term the claim is measured against, so it has to be one the equations
    // can speak about too.
    for (side, which) in [(identity.lhs, "left-hand"), (identity.rhs, "right-hand")] {
        if let Err(p) = check_preconditions(prog, side) {
            return Err(Failure::Side(p, which, prog.library().names[side].clone()));
        }
    }

    let tactic = compile(prog, file, proof)?;
    let lhs = tree(prog, identity.lhs);
    let rhs = tree(prog, identity.rhs);

    let env = Env::new(prog, opts.fuel, opts.check);
    let (got, script) = run_tactic(&env, &tactic, lhs.clone()).map_err(Failure::Ran)?;

    let misses = env.misses();
    if !misses.is_empty() {
        return Err(Failure::Missed(miss_report(&misses)));
    }

    // By effect, not by `==`. Phase 4 mints a fresh `SentenceIndex` for every
    // inline block, so the right-hand side's blocks can never share provenance
    // with anything the left-hand side rewrote into — and provenance is not
    // part of a term's identity.
    if !same_effect_seq(&got, &rhs) {
        return Err(Failure::NotReached(got));
    }

    // The claim that makes a script a derivation rather than a log: replaying
    // it against a fresh build reproduces the run exactly. Here `==` *is* the
    // right comparison, and the stronger one — a replay that merely had the
    // same effect would not be the same construction.
    let mut replayed = lhs;
    match apply_script(prog, &mut replayed, &script, opts.check) {
        Ok(()) if replayed == got => Ok(script),
        Ok(()) => Err(Failure::Replay("it produced a different tree".to_string())),
        Err(err) => Err(Failure::Replay(err.to_string())),
    }
}

fn compile(prog: &Program, file: &ProvenFile, proof: usize) -> Result<Tactic, Failure> {
    file.file
        .compile(&file.file.proofs[proof], prog)
        .map_err(|e| Failure::Proof(e.render_in(&file.source, &file.hant.display().to_string())))
}

fn tree(prog: &Program, root: SentenceIndex) -> Vec<Node> {
    build(prog.library(), root, &mut HashSet::new())
}

impl Failure {
    fn render(
        &self,
        prog: &Program,
        identity: &Identity,
        file: &ProvenFile,
        proof: usize,
        opts: &Options,
    ) -> Vec<String> {
        let mut out = Vec::new();
        match self {
            Failure::Side(p, which, name) => {
                let lines = precondition_explanation(*p, name);
                out.push(format!("  the {} side cannot be rewritten.", which));
                out.push(String::new());
                out.push(format!("  {}", lines[0]));
                out.extend(lines[1..].iter().cloned());
            }
            Failure::Proof(rendered) => {
                out.push("  the proof does not compile.".to_string());
                out.push(String::new());
                out.extend(rendered.lines().map(|l| l.to_string()));
            }
            Failure::Ran(err) => {
                out.push(format!("  the proof did not run: {}", err));
                out.extend(cited(file, proof));
            }
            Failure::Missed(report) => {
                out.push("  an aimed step in the proof matched nothing.".to_string());
                out.push(String::new());
                out.extend(report.iter().map(|l| indented(l)));
                out.push(String::new());
                out.push(
                    "  Here that fails the proof rather than warning: a proof aimed at a"
                        .to_string(),
                );
                out.push(
                    "  tree it no longer describes is wrong even where the goal was reached."
                        .to_string(),
                );
                out.extend(cited(file, proof));
            }
            Failure::NotReached(got) => {
                out.push("  the proof ran, but did not reach the right-hand side.".to_string());
                out.extend(cited(file, proof));
                out.push(String::new());
                let want = tree(prog, identity.rhs);
                // Without origins: the two sides came from two sentences, so
                // every `<inline>` label differs and none of the differences
                // mean anything. `same_effect_seq` ignores them for the same
                // reason, and a listing being compared has to agree with the
                // comparison.
                let left = render_nodes(prog, got, opts.stack, true, false);
                let right = render_nodes(prog, &want, opts.stack, true, false);
                let rows = side_by_side(&left, &right, "what it reached", "the right-hand side");
                if rows.is_empty() {
                    // Two listings that read alike but are not the same by
                    // effect. That is a bug in one of them rather than in the
                    // proof, so show both rather than nothing at all.
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
            Failure::Replay(why) => {
                out.push("  the proof reached the right-hand side, but its derivation".to_string());
                out.push(format!("  does not replay: {}", why));
                out.push(String::new());
                out.push("  That is a bug in the rewriter, not in the proof.".to_string());
            }
        }
        out
    }
}

/// The proof as written, and where. What a reader needs to go and fix it.
fn cited(file: &ProvenFile, proof: usize) -> Vec<String> {
    let def = &file.file.proofs[proof];
    let (start, end) = def.span;
    let text = file.source[start..end.min(file.source.len())].trim();
    let line = file.source[..start].matches('\n').count() + 1;
    vec![
        String::new(),
        format!("  proof: {}", text),
        format!("   --> {}:{}", file.hant.display(), line),
    ]
}

/// Two spaces in front of a line, except an empty one — which would otherwise
/// become trailing whitespace in the report.
fn indented(line: &str) -> String {
    if line.is_empty() {
        String::new()
    } else {
        format!("  {}", line)
    }
}

fn short(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
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

/// Parses arguments and runs. The binary is one line over this.
pub(crate) fn cli() -> i32 {
    let mut opts = Options::default();
    let mut positional: Vec<String> = Vec::new();

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
            "--filter" => match value("--filter") {
                Some(v) => opts.filter = Some(v),
                None => return BROKEN,
            },
            "--tactics" => match value("--tactics") {
                Some(v) => opts.tactic_files.push(PathBuf::from(v)),
                None => return BROKEN,
            },
            "--fuel" => match value("--fuel").map(|raw| raw.parse()) {
                Some(Ok(v)) => opts.fuel = v,
                Some(Err(_)) => {
                    eprintln!("--fuel needs a number");
                    return BROKEN;
                }
                None => return BROKEN,
            },
            "--no-check" => opts.check = false,
            "--show-script" => opts.show_script = true,
            "--stack" => opts.stack = true,
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

    if positional.len() != 1 {
        usage();
        return BROKEN;
    }
    opts.dir = PathBuf::from(&positional[0]);

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
    eprintln!("Usage: prove <directory> [options]");
    eprintln!();
    eprintln!("  Checks that every `identity` stated in the corpus rooted at");
    eprintln!("  <directory>/main.hana has a proof in the `.hant` beside the");
    eprintln!("  `.hana` that states it, and that the proof discharges it.");
    eprintln!();
    eprintln!("  --filter <substr>    only identities whose name contains this.");
    eprintln!("  --tactics <file>     tactic definitions loaded before every .hant.");
    eprintln!("  --show-script        print each derivation, one step per line.");
    eprintln!("  --stack              show what each slot holds, in a failure diff.");
    eprintln!("  --fuel <n>           rule firings before giving up.");
    eprintln!("  --no-check           skip the net-stack-effect check on every step.");
    eprintln!("                       It is on by default here and opt-in in `rewrite`:");
    eprintln!("                       this is the tool whose job is to be sure.");
    eprintln!();
    eprintln!("Exit: 0 every identity proved, 1 one did not, 2 the corpus would not build.");
    eprintln!();
    eprintln!("A proof is found with `rewrite`, which addresses an identity's sides");
    eprintln!("by name:");
    eprintln!();
    eprintln!("  rewrite tests 'my_identity::lhs' -t 'cleanup' --show-script");
    eprintln!("  rewrite tests 'my_identity::rhs'");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A corpus in a temp directory, since discovery is about files on disk.
    struct Corpus(PathBuf);

    impl Corpus {
        fn new(name: &str, hana: &str, hant: Option<&str>) -> Corpus {
            let dir = std::env::temp_dir().join(format!("hanoi_prove_{}", name));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(dir.join("main.hana"), hana).unwrap();
            if let Some(hant) = hant {
                std::fs::write(dir.join("main.hant"), hant).unwrap();
            }
            Corpus(dir)
        }

        fn write(&self, name: &str, text: &str) -> &Corpus {
            std::fs::write(self.0.join(name), text).unwrap();
            self
        }

        fn run(&self) -> (i32, String) {
            self.run_with(Options {
                dir: self.0.clone(),
                ..Options::default()
            })
        }

        fn run_with(&self, mut opts: Options) -> (i32, String) {
            opts.dir = self.0.clone();
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

    /// `is_bool ; is_bool` is `bool_result` and then an annihilation, which is
    /// what `cleanup` does in two steps.
    const TESTING_A_TEST: &str =
        "identity testing_a_test { is_bool is_bool } = { drop 0 push true };";

    #[test]
    fn a_correct_proof_passes() {
        let c = Corpus::new(
            "pass",
            TESTING_A_TEST,
            Some("proof testing_a_test = cleanup;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, OK, "{}", report);
        assert!(
            report.contains("identity testing_a_test ... ok"),
            "{}",
            report
        );
        assert!(report.contains("1 passed; 0 failed"), "{}", report);
    }

    /// The failure that matters: the tactic ran, and landed somewhere else.
    /// What the report owes is the difference, not the fact of it.
    #[test]
    fn a_proof_that_lands_elsewhere_shows_the_difference() {
        let c = Corpus::new(
            "elsewhere",
            "identity foo { is_bool is_bool } = { drop 0 push false };",
            Some("proof foo = cleanup;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(
            report.contains("did not reach the right-hand side"),
            "{}",
            report
        );
        assert!(report.contains("what it reached"), "{}", report);
        assert!(report.contains("push true"), "{}", report);
        assert!(report.contains("push false"), "{}", report);
        // The proof is quoted back with where to go and fix it.
        assert!(report.contains("proof: cleanup"), "{}", report);
    }

    /// Provenance is not part of a term's identity, so a diff must not report
    /// two `<inline>` labels — which never match across two sentences — as the
    /// difference.
    #[test]
    fn a_failure_diff_does_not_report_provenance() {
        let c = Corpus::new(
            "provenance",
            "identity foo { pick 0 branch { push 1 } { push 2 } } \
             = { pick 0 branch { push 1 } { push 9 } };",
            Some("proof foo = id;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(!report.contains("<inline>"), "{}", report);
        assert!(report.contains("push 2"), "{}", report);
        assert!(report.contains("push 9"), "{}", report);
    }

    #[test]
    fn an_identity_with_no_proof_is_reported() {
        let c = Corpus::new(
            "unproved",
            "identity a { drop 0 } = { drop 0 };\nidentity b { drop 0 } = { drop 0 };",
            Some("proof a = id;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("has no proof of `b`"), "{}", report);
        assert!(report.contains("proof b = <tactic>;"), "{}", report);
    }

    #[test]
    fn a_missing_hant_says_what_to_write() {
        let c = Corpus::new("no_hant", TESTING_A_TEST, None);
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("has no proofs"), "{}", report);
        assert!(
            report.contains("proof testing_a_test = <tactic>;"),
            "{}",
            report
        );
    }

    #[test]
    fn a_proof_of_an_identity_stated_elsewhere_says_where() {
        let c = Corpus::new(
            "elsewhere_file",
            "mod other;\nidentity here { drop 0 } = { drop 0 };",
            Some("proof here = id;\nproof there = id;"),
        );
        c.write("other.hana", "identity there { drop 0 } = { drop 0 };");
        c.write("other.hant", "proof there = id;");
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(
            report.contains("no identity `there` to prove here"),
            "{}",
            report
        );
        assert!(report.contains("stated in another file"), "{}", report);
    }

    #[test]
    fn an_unknown_identity_lists_what_the_file_does_state() {
        let c = Corpus::new(
            "unknown",
            TESTING_A_TEST,
            Some("proof testing_a_test = cleanup;\nproof nosuch = id;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("no identity `nosuch`"), "{}", report);
        assert!(
            report.contains("this file states: testing_a_test"),
            "{}",
            report
        );
    }

    /// Renaming a `.hana` orphans its proofs, and nothing else would notice.
    #[test]
    fn a_hant_beside_no_identity_is_reported() {
        let c = Corpus::new(
            "stray",
            TESTING_A_TEST,
            Some("proof testing_a_test = cleanup;"),
        );
        c.write("orphan.hant", "proof gone = id;");
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("orphan.hant' proves nothing"), "{}", report);
    }

    /// The divergence from `rewrite`, which treats a miss as a diagnostic and
    /// prints the tree anyway.
    #[test]
    fn an_aimed_step_that_misses_fails_the_proof() {
        let c = Corpus::new(
            "miss",
            TESTING_A_TEST,
            Some("proof testing_a_test = at(9, sink); cleanup;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("matched nothing"), "{}", report);
        assert!(
            report.contains("fails the proof rather than warning"),
            "{}",
            report
        );
    }

    /// ...and `try` is how a proof says a miss is acceptable.
    #[test]
    fn try_says_a_miss_is_acceptable() {
        let c = Corpus::new(
            "try",
            TESTING_A_TEST,
            Some("proof testing_a_test = try(at(9, sink)); cleanup;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, OK, "{}", report);
    }

    #[test]
    fn a_side_that_can_fail_is_refused_in_rewrites_own_words() {
        let c = Corpus::new(
            "fallible",
            "identity bad { assert } = { assert };",
            Some("proof bad = id;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(
            report.contains("the left-hand side cannot be rewritten"),
            "{}",
            report
        );
        assert!(report.contains("can fail"), "{}", report);
        assert!(report.contains("docs/totality.md"), "{}", report);
    }

    #[test]
    fn a_proof_that_does_not_compile_points_at_the_word() {
        let c = Corpus::new(
            "badproof",
            TESTING_A_TEST,
            Some("proof testing_a_test = nonesuch;"),
        );
        let (code, report) = c.run();
        assert_eq!(code, FAILED, "{}", report);
        assert!(report.contains("does not compile"), "{}", report);
        assert!(report.contains("main.hant:1:24"), "{}", report);
    }

    #[test]
    fn the_filter_selects_by_name() {
        let c = Corpus::new(
            "filter",
            "identity keep_me { drop 0 } = { drop 0 };\nidentity skip_me { drop 0 } = { drop 0 };",
            Some("proof keep_me = id;\nproof skip_me = id;"),
        );
        let (code, report) = c.run_with(Options {
            filter: Some("keep".to_string()),
            ..Options::default()
        });
        assert_eq!(code, OK, "{}", report);
        assert!(
            report.contains("1 passed; 0 failed; 1 filtered out"),
            "{}",
            report
        );
    }

    /// A tree missing three things should say so once, not over three runs.
    #[test]
    fn every_problem_is_reported_not_just_the_first() {
        let c = Corpus::new(
            "all_problems",
            "identity a { drop 0 } = { drop 0 };\nidentity b { drop 0 } = { drop 0 };",
            Some("proof nosuch = id;"),
        );
        let (_, report) = c.run();
        assert!(report.contains("no identity `nosuch`"), "{}", report);
        assert!(report.contains("has no proof of `a`"), "{}", report);
        assert!(report.contains("has no proof of `b`"), "{}", report);
    }

    /// A `.hana` that states nothing needs no `.hant`, which is nearly every
    /// file in the corpus.
    #[test]
    fn a_hana_that_states_nothing_needs_no_hant() {
        let c = Corpus::new("quiet", "sentence a { }", None);
        let (code, report) = c.run();
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("Proving 0 identities"), "{}", report);
    }

    #[test]
    fn a_corpus_that_will_not_build_is_a_different_exit_code() {
        let c = Corpus::new("broken", "sentence a { frobnicate }", None);
        let (code, _) = c.run();
        assert_eq!(code, BROKEN);
    }

    #[test]
    fn a_tactics_file_is_loaded_before_every_hant() {
        let c = Corpus::new(
            "prelude",
            TESTING_A_TEST,
            Some("proof testing_a_test = mine;"),
        );
        c.write("shared.tactics", "tactic mine = cleanup;");
        let (code, report) = c.run_with(Options {
            tactic_files: vec![c.0.join("shared.tactics")],
            ..Options::default()
        });
        assert_eq!(code, OK, "{}", report);
    }

    #[test]
    fn show_script_prints_the_derivation() {
        let c = Corpus::new(
            "script",
            TESTING_A_TEST,
            Some("proof testing_a_test = cleanup;"),
        );
        let (code, report) = c.run_with(Options {
            show_script: true,
            ..Options::default()
        });
        assert_eq!(code, OK, "{}", report);
        assert!(report.contains("derivation — 2 step(s)"), "{}", report);
        assert!(report.contains("bool_result"), "{}", report);
    }
}
