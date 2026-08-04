//! Two listings, lined up side by side.
//!
//! A rule firing is a splice: a handful of lines change in a tree that may be
//! thousands of lines long. Reprinting the whole listing at every step buries
//! that, so the stepper puts the tree before the firing next to the tree after
//! it and shows only where they differ, with a few lines of context either
//! side.
//!
//! The diff is **textual, over the rendered listing**, rather than structural
//! over the tree. That is a choice and not a shortcut. A structural diff would
//! have to decide what "the same node" means across a rewrite that splices,
//! reorders and reparents — which is the question the rewriter is itself
//! answering, so any answer here would be a second, quieter opinion about it.
//! The listing is also what the reader is looking at, gutter and all, and a
//! depth shifting by one is part of what the firing did.

/// Identical lines kept either side of a change.
const CONTEXT: usize = 3;

/// The widest either column may get before lines are elided. Listings are
/// narrow; `--stack` ones are not, and two of those side by side would run off
/// any terminal.
const MAX_COL: usize = 56;

/// The longest run of changed lines that gets aligned line by line.
///
/// The alignment is a quadratic-space LCS, which is fine for the tens of lines
/// a rule firing touches and not fine for a `distribute_branch` that copied a
/// thousand-line arm. Past this the two runs are shown as one block change,
/// which is what they are.
const MAX_LCS: usize = 400;

/// One row of the side-by-side view.
#[derive(Debug, PartialEq, Clone, Copy)]
enum Row {
    /// The same line in both, by index into each.
    Same(usize, usize),
    /// Only in the left listing: a line the firing removed.
    Left(usize),
    /// Only in the right: a line it added.
    Right(usize),
    /// An elided run of identical lines.
    Skip(usize),
}

/// The side-by-side listing, or nothing at all if the two are identical.
pub(crate) fn side_by_side(
    before: &[String],
    after: &[String],
    left_label: &str,
    right_label: &str,
) -> Vec<String> {
    let rows = align(before, after);
    if rows.iter().all(|r| matches!(r, Row::Same(..))) {
        return Vec::new();
    }
    render(&collapse(rows), before, after, left_label, right_label)
}

/// Pairs the two listings up, line for line.
///
/// The common prefix and suffix are taken first, which is what keeps this cheap
/// on a large tree: a firing changes one region, so whatever is left over after
/// trimming both ends is the size of the rewrite rather than the size of the
/// listing.
fn align(before: &[String], after: &[String]) -> Vec<Row> {
    let head = before.iter().zip(after).take_while(|(a, b)| a == b).count();
    let tail = before[head..]
        .iter()
        .rev()
        .zip(after[head..].iter().rev())
        .take_while(|(a, b)| a == b)
        .count();

    let mut rows: Vec<Row> = (0..head).map(|i| Row::Same(i, i)).collect();
    rows.extend(lcs(
        &before[head..before.len() - tail],
        &after[head..after.len() - tail],
        head,
    ));
    rows.extend((0..tail).map(|i| Row::Same(before.len() - tail + i, after.len() - tail + i)));
    rows
}

/// Longest common subsequence of the two changed runs, `at` lines in.
fn lcs(before: &[String], after: &[String], at: usize) -> Vec<Row> {
    let (n, m) = (before.len(), after.len());
    if n.max(m) > MAX_LCS {
        return (0..n)
            .map(|i| Row::Left(at + i))
            .chain((0..m).map(|j| Row::Right(at + j)))
            .collect();
    }

    // table[i][j] is the length of the LCS of before[i..] and after[j..].
    let mut table = vec![0usize; (n + 1) * (m + 1)];
    let cell = |i: usize, j: usize| i * (m + 1) + j;
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            table[cell(i, j)] = if before[i] == after[j] {
                table[cell(i + 1, j + 1)] + 1
            } else {
                table[cell(i + 1, j)].max(table[cell(i, j + 1)])
            };
        }
    }

    let mut rows = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < n && j < m {
        if before[i] == after[j] {
            rows.push(Row::Same(at + i, at + j));
            i += 1;
            j += 1;
        } else if table[cell(i + 1, j)] >= table[cell(i, j + 1)] {
            // Prefer spending the left line, so a replacement reads as a
            // removal beside an addition rather than the other way round.
            rows.push(Row::Left(at + i));
            i += 1;
        } else {
            rows.push(Row::Right(at + j));
            j += 1;
        }
    }
    rows.extend((i..n).map(|i| Row::Left(at + i)));
    rows.extend((j..m).map(|j| Row::Right(at + j)));
    rows
}

/// Elides runs of identical lines, keeping [`CONTEXT`] of them at each change.
fn collapse(rows: Vec<Row>) -> Vec<Row> {
    let mut out: Vec<Row> = Vec::new();
    let mut i = 0;
    while i < rows.len() {
        if !matches!(rows[i], Row::Same(..)) {
            out.push(rows[i]);
            i += 1;
            continue;
        }
        let start = i;
        while i < rows.len() && matches!(rows[i], Row::Same(..)) {
            i += 1;
        }
        // A run at either end of the listing only has context on one side; one
        // in the middle has it on both.
        let lead = if start == 0 { 0 } else { CONTEXT };
        let trail = if i == rows.len() { 0 } else { CONTEXT };
        let run = i - start;
        if run <= lead + trail {
            out.extend(&rows[start..i]);
            continue;
        }
        out.extend(&rows[start..start + lead]);
        out.push(Row::Skip(run - lead - trail));
        out.extend(&rows[i - trail..i]);
    }
    out
}

fn render<'a>(
    rows: &[Row],
    before: &'a [String],
    after: &'a [String],
    left_label: &str,
    right_label: &str,
) -> Vec<String> {
    let shown = |row: &Row| -> Vec<&str> {
        match row {
            Row::Same(a, b) => vec![before[*a].as_str(), after[*b].as_str()],
            Row::Left(a) => vec![before[*a].as_str()],
            Row::Right(b) => vec![after[*b].as_str()],
            Row::Skip(_) => vec![],
        }
    };

    // Two listings side by side is twice the width, and a `--stack` listing
    // spends thirty columns on right-aligned padding that says nothing here.
    // Whatever indentation every shown line shares is not telling them apart.
    let indent = rows
        .iter()
        .flat_map(&shown)
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.len() - line.trim_start().len())
        .min()
        .unwrap_or(0);
    let cut = |line: &'a str| line.get(indent..).unwrap_or("");

    let width = rows
        .iter()
        .flat_map(&shown)
        .map(|line| cut(line).chars().count())
        .max()
        .unwrap_or(0)
        .clamp(left_label.chars().count().min(MAX_COL), MAX_COL);

    let mut out = vec![
        format!("    {:<w$} ┃   {}", left_label, right_label, w = width),
        format!("  {}─╂─{}", "─".repeat(width + 2), "─".repeat(width + 2)),
    ];

    let mut i = 0;
    while i < rows.len() {
        match &rows[i] {
            Row::Same(a, b) => {
                out.push(line(' ', cut(&before[*a]), ' ', cut(&after[*b]), width));
                i += 1;
            }
            Row::Skip(n) => {
                out.push(format!(
                    "    {:<w$} ┃",
                    format!("⋮ {} unchanged line{}", n, if *n == 1 { "" } else { "s" }),
                    w = width
                ));
                i += 1;
            }
            // A run of removals followed by a run of additions is one change,
            // so the two are zipped onto the same rows rather than stacked.
            Row::Left(_) | Row::Right(_) => {
                let (mut gone, mut new) = (Vec::new(), Vec::new());
                while i < rows.len() {
                    match &rows[i] {
                        Row::Left(a) => gone.push(cut(&before[*a])),
                        Row::Right(b) => new.push(cut(&after[*b])),
                        _ => break,
                    }
                    i += 1;
                }
                for k in 0..gone.len().max(new.len()) {
                    let (lmark, ltext) = match gone.get(k) {
                        Some(text) => ('-', *text),
                        None => (' ', ""),
                    };
                    let (rmark, rtext) = match new.get(k) {
                        Some(text) => ('+', *text),
                        None => (' ', ""),
                    };
                    out.push(line(lmark, ltext, rmark, rtext, width));
                }
            }
        }
    }
    // The left column is padded to line the two up; the right one has nothing
    // to line up against, so it keeps no trailing space.
    out.iter().map(|l| l.trim_end().to_string()).collect()
}

fn line(lmark: char, ltext: &str, rmark: char, rtext: &str, width: usize) -> String {
    format!(
        "  {} {:<w$} ┃ {} {}",
        lmark,
        elide(ltext, width),
        rmark,
        elide(rtext, width),
        w = width
    )
}

/// Cuts a line to `width` characters, the last of which says it was cut.
fn elide(text: &str, width: usize) -> String {
    if text.chars().count() <= width {
        return text.to_string();
    }
    let cut = text
        .char_indices()
        .nth(width.saturating_sub(1))
        .map(|(i, _)| i)
        .unwrap_or(0);
    format!("{}…", &text[..cut])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lines(text: &str) -> Vec<String> {
        text.lines().map(str::to_string).collect()
    }

    /// The diff with its two header lines dropped.
    fn diff(before: &str, after: &str) -> Vec<String> {
        let out = side_by_side(&lines(before), &lines(after), "before", "after");
        if out.is_empty() {
            return out;
        }
        out[2..].to_vec()
    }

    #[test]
    fn identical_listings_diff_to_nothing() {
        assert!(side_by_side(&lines("a\nb"), &lines("a\nb"), "l", "r").is_empty());
    }

    #[test]
    fn a_replacement_puts_the_two_lines_on_one_row() {
        let rows = diff("a\nb\nc", "a\nB\nc");
        assert_eq!(rows.len(), 3, "{:#?}", rows);
        assert!(rows[1].contains("- b"), "{}", rows[1]);
        assert!(rows[1].contains("+ B"), "{}", rows[1]);
        // Context is shown on both sides of the change.
        assert!(rows[0].contains('a') && rows[2].contains('c'));
    }

    #[test]
    fn an_insertion_leaves_the_left_column_blank() {
        let rows = diff("a\nc", "a\nb\nc");
        let changed = rows.iter().find(|r| r.contains("+ b")).expect("the insert");
        assert!(!changed.contains('-'), "nothing was removed: {}", changed);
    }

    #[test]
    fn a_long_run_of_identical_lines_is_elided() {
        let before: Vec<String> = (0..40).map(|i| format!("line {}", i)).collect();
        let mut after = before.clone();
        after[20] = "changed".to_string();

        let out = side_by_side(&before, &after, "l", "r");
        let skipped: Vec<&String> = out.iter().filter(|l| l.contains('⋮')).collect();
        assert_eq!(skipped.len(), 2, "one elision either side: {:#?}", out);
        // The change, its context, two elisions, and the two header lines.
        assert_eq!(out.len(), 2 + 1 + 2 * CONTEXT + 2, "{:#?}", out);
        assert!(out.iter().any(|l| l.contains("line 17")), "{:#?}", out);
        assert!(!out.iter().any(|l| l.contains("line 16")), "{:#?}", out);
    }

    #[test]
    fn a_change_at_the_top_keeps_only_the_context_below_it() {
        let before: Vec<String> = (0..40).map(|i| format!("line {}", i)).collect();
        let mut after = before.clone();
        after[0] = "changed".to_string();

        let out = side_by_side(&before, &after, "l", "r");
        assert_eq!(out.len(), 2 + 1 + CONTEXT + 1, "{:#?}", out);
        assert!(out.last().unwrap().contains('⋮'), "{:#?}", out);
    }

    #[test]
    fn a_long_line_is_elided_rather_than_wrapped() {
        let long = "x".repeat(MAX_COL + 20);
        let rows = diff(&long, "short");
        assert!(rows[0].contains('…'), "{}", rows[0]);
        assert!(
            rows[0].chars().count() < 2 * MAX_COL + 12,
            "row is {} wide",
            rows[0].chars().count()
        );
    }

    #[test]
    fn a_change_too_big_to_align_is_shown_as_one_block() {
        // The LCS is quadratic in the size of the change, so past a bound the
        // two runs are shown whole rather than paired up. Nothing is dropped.
        let before: Vec<String> = (0..MAX_LCS + 10).map(|i| format!("a {}", i)).collect();
        let after: Vec<String> = (0..MAX_LCS + 10).map(|i| format!("b {}", i)).collect();
        let out = side_by_side(&before, &after, "l", "r");
        assert_eq!(out.len(), 2 + MAX_LCS + 10);
        assert!(out[2].contains("- a 0") && out[2].contains("+ b 0"));
    }

    #[test]
    fn the_columns_line_up_even_when_one_side_runs_out() {
        let rows = diff("a\nb\nc\nd", "a\nd");
        for row in &rows {
            let (left, right) = row.split_once('┃').expect("a column separator");
            assert_eq!(
                left.chars().count(),
                rows[0].split_once('┃').unwrap().0.chars().count()
            );
            // A row with nothing on the right keeps no trailing space.
            assert!(right.is_empty() || right.starts_with(' '), "{:?}", right);
        }
    }
}
