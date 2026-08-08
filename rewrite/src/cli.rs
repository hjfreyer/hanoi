//! `rewrite` — work the goal an identity states, and watch a strategy try it.
//!
//! Argument parsing and nothing else; [`crate::goal`] is where the work happens
//! and where the reasoning lives.
//!
//! The listing this prints is a debugging aid, not a source generator: the
//! output does not parse, because a dipped block operates below its hidden
//! region and so cannot be spliced into the enclosing instruction stream as-is.
//! What it gives you is the whole call tree in one listing instead of a set of
//! `SentenceIndex` references to chase by hand.
//!
//! Its sibling is `prove`, which checks every identity a corpus states against
//! the proof written beside it. Both sit on the `rewrite` library, and both run
//! the same strategy over the same goal — what differs is where the strategy
//! came from and what is done about a goal that does not close.

use std::env;
use std::fs;
use std::path::Path;
use std::process;

use crate::program::Program;
use crate::script::{Definitions, PRELUDE};
use crate::{Options, goal, load, rule_listing, tactic_listing};

pub fn run() -> i32 {
    let mut opts = Options::default();
    let mut tactic_files: Vec<String> = Vec::new();
    let mut positional: Vec<String> = Vec::new();
    let mut list_rules = false;
    let mut list_tactics = false;

    let args: Vec<String> = env::args().skip(1).collect();
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        let mut value = |name: &str| -> String {
            i += 1;
            match args.get(i) {
                Some(v) => v.clone(),
                None => {
                    eprintln!("{} needs a value", name);
                    process::exit(1);
                }
            }
        };
        match arg {
            "-t" | "--tactic" => opts.tactic = value("-t"),
            "--tactics" => tactic_files.push(value("--tactics")),
            "--fuel" => {
                let raw = value("--fuel");
                opts.fuel = match raw.parse() {
                    Ok(v) => v,
                    Err(_) => {
                        eprintln!("--fuel needs a number, found '{}'", raw);
                        process::exit(1);
                    }
                };
            }
            "--trace" => opts.trace = true,
            "--step" => opts.step = true,
            "--stack" => opts.stack = true,
            "--width" => {
                let raw = value("--width");
                opts.width = match raw.parse() {
                    Ok(v) => v,
                    Err(_) => {
                        eprintln!("--width needs a number, found '{}'", raw);
                        process::exit(1);
                    }
                };
            }
            "--check" => opts.check = true,
            "--show-script" => opts.show_script = true,
            "--list-rules" => list_rules = true,
            "--list-tactics" => list_tactics = true,
            flag if flag.starts_with('-') => {
                eprintln!("Unknown flag: {}", flag);
                usage();
                process::exit(1);
            }
            other => positional.push(other.to_string()),
        }
        i += 1;
    }

    let mut defs = Definitions::new();
    if let Err(err) = defs.load(PRELUDE) {
        eprintln!("{}", err.render(PRELUDE));
        eprintln!("(this is a bug in the built-in prelude)");
        process::exit(1);
    }
    for path in &tactic_files {
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(err) => {
                eprintln!("Error reading '{}': {}", path, err);
                process::exit(1);
            }
        };
        if let Err(err) = defs.load(&source) {
            eprint!("{}", err.render(&source));
            process::exit(1);
        }
    }

    if list_rules {
        for line in rule_listing() {
            println!("{}", line);
        }
        return 0;
    }
    if list_tactics {
        for line in tactic_listing(&defs) {
            println!("{}", line);
        }
        return 0;
    }

    if positional.len() != 2 {
        usage();
        process::exit(1);
    }

    let (_sources, library) = match load(Path::new(&positional[0])) {
        Ok(pair) => pair,
        Err(err) => {
            eprint!("{}", err);
            if !err.ends_with('\n') {
                eprintln!();
            }
            process::exit(1);
        }
    };
    // An identity, and only an identity. Everything this tool does is about a
    // goal, so a term worth looking at is a term worth stating one over — and a
    // reflexive `identity probe { jump X } = { jump X };` gives back the
    // one-sided listing this positional used to take a sentence for.
    let index = match library.identity_by_name(&positional[1]) {
        Ok(idx) => idx,
        Err(err) => {
            eprintln!("{}", err);
            process::exit(1);
        }
    };
    let identity = &library.identities[index];

    let prog = Program::new(&library);

    // After the library, because a term may name a sentence — `share { jump
    // foo }` needs `foo`'s arity to know how wide a window it reads. Everything
    // else about a strategy is still checked here rather than at run time.
    let strategy = match defs.compile_proof(&opts.tactic, Some(&prog)) {
        Ok(s) => s,
        Err(err) => {
            eprint!("{}", err.render(&opts.tactic));
            process::exit(1);
        }
    };
    // The comparison is up to inlining, and this is what does it. From the
    // prelude, where it is `repeat(bu(each(unfold)))`.
    let inline = match defs.compile_with("unfold_all", Some(&prog)) {
        Ok(t) => t,
        Err(err) => {
            eprint!("{}", err.render("unfold_all"));
            eprintln!("(this is a bug in the built-in prelude)");
            process::exit(1);
        }
    };

    let stdout = std::io::stdout();
    let mut handle = stdout.lock();
    match goal::run(&prog, identity, &strategy, &inline, &opts, &mut handle) {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error writing the report: {}", err);
            1
        }
    }
}

fn usage() {
    eprintln!("Usage: rewrite <directory> <identity> [-t <strategy>] [options]");
    eprintln!();
    eprintln!("  Works the goal an `identity` states: two terms, and the claim");
    eprintln!("  that they are equal. <identity> is a fully qualified name or an");
    eprintln!("  unambiguous trailing part of one.");
    eprintln!();
    eprintln!("  What closes here is what goes in the `.hant`, character for");
    eprintln!("  character. A goal left standing is the answer, not an error;");
    eprintln!("  `prove` is the tool whose job is to say no.");
    eprintln!();
    eprintln!("  -t, --tactic <expr>  the strategy to try. A bare tactic runs it on");
    eprintln!("                       the left and compares, which is what a proof");
    eprintln!("                       written bare has always meant. Default");
    eprintln!("                       `default`, which shows the two sides as written.");
    eprintln!("  --tactics <file>     load `tactic`/`strategy` definitions.");
    eprintln!("  --list-rules         the rules a tactic can place.");
    eprintln!("  --list-tactics       the named tactics currently defined.");
    eprintln!("  --fuel <n>           rule firings before giving up, over the whole");
    eprintln!("                       strategy rather than each run in it.");
    eprintln!("  --trace              print how often each rule fired.");
    eprintln!("  --step               walk the derivation one rule firing at a time.");
    eprintln!("  --check              verify every step preserves net stack effect.");
    eprintln!("  --show-script        print the derivation, one step per line.");
    eprintln!(
        "  --stack              show what each slot holds, with equal values sharing a name."
    );
    eprintln!("  --width <n>          how wide each column of a side-by-side listing");
    eprintln!("                       may get before a line is elided. Default 56,");
    eprintln!("                       which fits two columns in eighty.");
    eprintln!();
    eprintln!("Strategies are a sequence of moves over the goal, `a; b; c`:");
    eprintln!("  <tactic>, exact(t)   drive the left-hand side");
    eprintln!("  rhs(t)               drive the right-hand side");
    eprintln!("  normalize(t)         drive both with the same tactic");
    eprintln!("  peel                 narrow to what the two sides do not share");
    eprintln!("  inline               unfold every call on both sides");
    eprintln!("and these fork the goal, so they come last:");
    eprintln!("  descend(body: s), descend(then: s, else: s), s | s");
    eprintln!("An arm left out of `descend` is a claim that it already matches,");
    eprintln!("which is checked: `descend(else: cleanup)` proves the else arm and");
    eprintln!("holds the then arms to being equal already.");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  rewrite tests two_spellings_of_one_test");
    eprintln!("  rewrite tests two_spellings_of_one_test -t 'normalize(cleanup)'");
    eprintln!("  rewrite tests testing_a_test_by_name -t 'cleanup; rhs(unfold_all)'");
    eprintln!("  rewrite tests a_test_inside_an_arm -t 'peel; descend(then: cleanup)'");
    eprintln!("  rewrite tests copying_a_constant -t 'dips; factoring' --step");
}
