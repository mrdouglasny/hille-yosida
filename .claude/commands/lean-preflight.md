# Lean Preflight Check

Run a comprehensive preflight check before starting Lean 4 development work.

## Step 1: Check MCP Connectivity

**IMPORTANT**: The Lean LSP requires a file-based call to set the project path before other LSP tools work.
Run `lean_file_outline` on the project's root `.lean` file (e.g., `lean/SpecialFunctions.lean`) FIRST,
before any parallel MCP checks. This primes the LSP.

### 1a. Lean LSP (must run first, alone)
First call `lean_file_outline` on the main .lean file to set the project path.
Then call `lean_local_search` for a known declaration (e.g., `Real.Gamma`) to verify search works.
- Report: **Lean LSP**: OK / FAILED (error message)

### 1b-1c. Gemini Chat & Deep Think (can run in parallel after 1a)
Run `chat_gemini` with "Reply OK" and `deep_think_gemini` with "Reply OK" (timeout 30s) in parallel.
- Report: **Gemini Chat**: OK / FAILED (error message)
- Report: **Gemini Deep Think**: OK (Xs) / FAILED (error message)

## Step 2: Git Status & Branches

### 2a. Working tree status
Run `git status` to check for uncommitted changes, staged files, etc.
- Report: clean / dirty (list changes)

### 2b. Current branch & recent commits
Run `git log --oneline -5` to show recent history.

### 2c. Related branches
Run `git branch -a` and look for branches related to the current work (lean, mathlib, special-functions, etc.).
- Report any branches that might have relevant in-progress work.
- If there are feature branches, show their last commit date relative to main.

### 2d. Upstream sync
Check if the current branch is up to date with its remote tracking branch.
Run `git fetch --dry-run 2>&1` to check for upstream changes without pulling.

### 2e. Research-dev submodule
Run `./research-dev/update.sh --check` to see if the submodule has upstream updates or skill sync issues.
- Report: **research-dev**: up to date / updates available / skills out of sync

## Step 3: Toolchain & Mathlib

### 3a. Lean toolchain
Read `lean/lean-toolchain` and report the current Lean version.
Run `elan show` (if available) to verify the installed toolchain matches.

### 3b. Mathlib version
Read `lean/lakefile.lean` and extract the Mathlib commit hash.
Check if this is recent by running:
```bash
cd lean && git -C .lake/packages/mathlib log --oneline -1 2>/dev/null
```
If `.lake/packages/mathlib` doesn't exist, note that `lake build` hasn't been run yet.

### 3c. Mathlib update check
Check if a newer Mathlib is available:
```bash
cd lean && lake update --dry-run 2>&1 | head -20
```
If `--dry-run` isn't supported, just report the current pinned commit and suggest checking manually.
- Report: **Mathlib**: pinned at `<hash>` (up to date / update available / unknown)

## Step 4: Build Check

Run `lake build` from the `lean/` directory.
- If it succeeds: report **Build**: OK (time taken)
- If it fails: report **Build**: FAILED and show the first error
- If it's already cached: report **Build**: OK (cached)

## Step 5: Project Status Snapshot

### 5a. Sorry count
Search all `.lean` files under `lean/SpecialFunctions/` for `sorry` (excluding comments).
- Report: **Sorries**: N remaining (list files with counts)

### 5b. Axiom check
For any theorem files, note if `lean_verify` should be run on key theorems.

### 5c. TODO tasks
List files in `TODO/` directory (if it exists) and show their priority/status.

### 5d. Recent history
Read the last 10-15 lines of `history/claude_project_work.md` (if it exists) to show what was worked on recently.

## Step 6: Summary Report

Present a compact status dashboard:

```
=== Lean Preflight Check ===

MCPs:
  Lean LSP:        OK / FAILED
  Gemini Chat:     OK / FAILED
  Gemini DeepThink: OK / FAILED

Repository:
  Branch:      main (clean/dirty)
  Upstream:    up to date / behind by N commits
  Branches:    N total (list any feature branches)
  research-dev: up to date / updates available

Toolchain:
  Lean:        v4.X.Y
  Mathlib:     <short-hash> (status)

Build:         OK / FAILED / NOT RUN

Codebase:
  Sorries:     N remaining
  TODOs:       N pending tasks

Recent Work:
  <last 2-3 history entries>

Ready to work: YES / NO (issues: ...)
```

If any check fails, list the issues at the bottom with suggested fixes.
