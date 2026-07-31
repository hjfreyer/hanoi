---
name: jj-vcs
description: Activate first on any VCS operation (commit, status, branch, push) if a .jj/ directory exists — this is a Jujutsu repo, and jj commands should always be preferred over git commands. Contains the safety rules for working with jj.
allowed-tools: Bash(jj *)
---

# Jujutsu (jj) Version Control System

This skill helps you work with Jujutsu, a Git-compatible VCS with mutable commits and automatic rebasing.

## Automated/Agent Environment

When running as an agent:

1. **Use `--no-pager`** to prevent commands from opening an interactive pager (like `less`), which will hang the agent:

```bash
# Always use --no-pager on commands that produce output
jj --no-pager log          # NOT: jj log
jj --no-pager diff         # NOT: jj diff
jj --no-pager show <id>    # NOT: jj show <id>
```

2. **Use `-m` flags** to provide messages inline rather than relying on editor prompts:

```bash
# Always use -m to avoid editor prompts
jj desc -m "message"      # NOT: jj desc
jj squash -m "message"    # NOT: jj squash (which opens editor)
```

Editor-based commands will fail in non-interactive environments.

3. **Verify operations with `jj --no-pager st`** after mutations (`squash`, `abandon`, `rebase`, `restore`) to confirm the operation succeeded.

## Core Concepts

### The Working Copy is a Commit

In jj, your working directory is always a commit (referenced as `@`). Changes are automatically snapshotted when you run any jj command. There is no staging area.

### Commits Are Mutable

Unlike git, jj commits can be freely modified after creation. You can update descriptions, squash changes, rebase, and absorb — all without creating new commits. See "Essential Workflow" below for the recommended working pattern.

### Change IDs vs Commit IDs

- **Change ID**: A stable identifier (like `tqpwlqmp`) that persists when a commit is rewritten — prefer these when referencing commits
- **Commit ID**: A content hash (like `3ccf7581`) that changes when commit content changes

### Revsets

jj uses a revset language to select commits in commands. Common revsets:

- `@` — the working copy commit
- `@-` — the parent of the working copy
- `::@` — all ancestors of `@`
- `@::` — all descendants of `@`
- `trunk()..@` — commits between trunk and `@` (your branch)
- `bookmarks()` — all commits with bookmarks

Use revsets with `-r` flags: `jj --no-pager log -r 'trunk()..@'`

## Essential Workflow

### Starting Work: A Fresh, Undescribed Change

Do all work in a fresh change with no description — write the message after the change is done, not before.

Before making any changes, check where you are:

```bash
jj --no-pager st
```

- **Current change has a description** — it belongs to already-finished work. Run `jj new` to move to a clean change.
- **Current change is non-empty and undescribed** — there are changes here from earlier that were never committed. Investigate before building on top of them.
- **Current change is empty and undescribed** — you're ready. Start coding; jj snapshots everything automatically, no staging or intermediate commits needed.

### Finishing Work: Squash or Commit

Once the change is ready, decide where it belongs:

- **An amendment to the previous commit** — fold it in: `jj squash`
- **A separate, logical change** — describe it and move on: `jj commit -m "description"` (this sets the description on `@` and opens a fresh, empty, undescribed change on top — no separate `jj new` needed)

To decide which, check whether the previous commit's existing description still accurately covers the combined diff. If it does — you're filling in something that commit was missing, fixing a bug introduced by it, or reacting to review feedback on it — squash. If the new work is something someone might reasonably want to review, revert, or rebase independently of the previous commit, commit it separately. When genuinely unsure, prefer squashing: don't split changes into commits just because they touch different files or concepts. A commit can bundle multiple related edits; over-splitting produces noisy history that's harder to review than a slightly larger, coherent commit.

### Viewing History

```bash
# View recent commits
jj --no-pager log

# View with patches
jj --no-pager log -p

# View specific commit
jj --no-pager show <change-id>

# View diff of working copy (use --git for familiar +/- format)
jj --no-pager diff --git
```

The default `jj diff` output uses a side-by-side line number format (e.g. `26   26:`) that looks very different from git's `+`/`-` prefix format. This is normal and correct, not corrupted or stale content — but to avoid confusion, use `jj --no-pager diff --git` to get standard unified diff format with `+`/`-` lines.

### Moving Between Commits

```bash
# Create a new empty commit on top of current
jj new

# Create a new empty commit before the current one (inserted as its new parent)
jj prev

# Create a new empty commit after the current one
jj next
```

## Refining Commits

### Squashing Changes

Move changes from current commit into its parent:

```bash
# Squash all changes into parent
jj squash
```

**Note**: `jj squash -i` opens an interactive UI and will hang in agent environments. Avoid it.

### Splitting Commits

**Warning**: `jj split` is interactive and will hang in agent environments. To divide a commit, use `jj restore` to move changes out, then create separate commits manually.

### Absorbing Changes

Automatically distribute changes to the commits that last modified those lines:

```bash
# Absorb working copy changes into appropriate ancestor commits
jj absorb
```

### Abandoning Commits

Remove a commit entirely (descendants are rebased to its parent):

```bash
jj abandon <change-id>
```

### Undoing Operations

Reverse the last jj operation:

```bash
jj undo
```

This reverts the repository to its state before the previous command. Useful for recovering from mistakes like accidental `abandon`, `squash`, or `rebase`.

### Rebasing Commits

Move commits to a different parent:

```bash
# Rebase current branch onto a destination
jj rebase -d <destination>

# Rebase a specific revision (without descendants) onto a destination
jj rebase -r <change-id> -d <destination>

# Rebase a revision and all its descendants
jj rebase -s <change-id> -d <destination>

# Rebase onto trunk (common: update your branch to latest main)
jj rebase -d main
```

### Restoring Files

Discard changes to specific files or restore files from another revision:

```bash
# Discard all uncommitted changes in working copy (restore from parent)
jj restore

# Discard changes to specific files
jj restore path/to/file.txt

# Restore files from a specific revision
jj restore --from <change-id> path/to/file.txt
```

## Handling Conflicts

jj allows committing conflicts — you can resolve them later:

```bash
# View conflicts
jj --no-pager st
```

**Agent conflict resolution**: Do not use `jj resolve` (interactive). Instead, edit the conflicted files directly to remove conflict markers, then run `jj --no-pager st` to verify resolution.

## Preserving Commit Quality

Because commits are mutable, refine them before considering work done:

1. **Review your commit**: after `jj commit -m`, the finished commit is the parent, not `@` — use `jj --no-pager show @-` or `jj --no-pager diff --git -r @-`
2. **Does the message still match the diff?** If the commit grew beyond what its description covers, update the description — don't split just to keep things "atomic"
3. **Is the message clear?** Use imperative verb phrase in sentence case format with no full stop: e.g. "Add login endpoint", "Fix null pointer in payment processor", "Remove deprecated API endpoints"
4. **Are there unrelated changes?** Use `jj restore` to move changes out, then create separate commits
5. **Should changes be elsewhere?** Use `jj squash` or `jj absorb`

## Quick Reference

| Action | Command |
|--------|---------|
| Check where you are | `jj --no-pager st` |
| Start a fresh change | `jj new` |
| Finish & describe change | `jj commit -m "message"` |
| Edit an existing description | `jj desc -m "message"` |
| View log | `jj --no-pager log` |
| View diff | `jj --no-pager diff --git` |
| Edit commit | `jj edit <id>` |
| Squash into parent | `jj squash` |
| Auto-distribute | `jj absorb` |
| Rebase | `jj rebase -d <destination>` |
| Abandon commit | `jj abandon <id>` |
| Undo last operation | `jj undo` |
| Restore files | `jj restore [paths]` |

## Best Practices Summary

1. **Describe last**: Work in a fresh, undescribed change; only add a message once you know whether it's a squash or a `jj commit`
2. **Squash by default**: Only commit separately when the work is something someone would want to review, revert, or rebase on its own
3. **Use change IDs**: They're stable across rewrites
4. **Refine commits**: Leverage mutability for clean history
5. **Embrace the workflow**: No staging area, no stashing - just commits
