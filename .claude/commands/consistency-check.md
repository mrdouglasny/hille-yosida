# Skill: Consistency Check

Run comprehensive consistency checks across the codebase, including both automated and LLM-based semantic analysis. **This skill should fix easy issues automatically.**

## Invocation
```
/consistency-check [scope]
```

Scope options:
- `quick` - Run fast automated checks only (~5 seconds)
- `full` - Run all checks including LLM analysis and auto-fix (~2-5 minutes)
- `code-theory` - Focus on code-to-LaTeX correspondence
- `verification` - Check VERIFICATION.md files are current
- `locks` - Check agent lock status

## Step 1: Run Automated Checks (DO THIS FIRST)

**IMMEDIATELY run this command when the skill is invoked:**
```bash
bash scripts/check_consistency.sh
```

This runs both shell-based and Python semantic checks (~5 seconds) and saves a combined report to:
- **Latest**: `logs/consistency_check_latest.md` (always current)
- **Dated**: `logs/consistency_check_YYYYMMDD.md` (archived)

## Step 2: Review the Report

Read the generated report using the Read tool on `logs/consistency_check_latest.md`.

The report includes:
1. **Shell checks**: PDF freshness, Julia headers, versioned files, VERIFICATION.md, Lean sorries
2. **Semantic checks**: Broken links, citations, verification freshness, lock staleness, TODO/DONE consistency

## Step 3: Auto-Fix Easy Issues

**IMPORTANT**: After reviewing the report, automatically fix these issue types:

### Broken Links (auto-fix)
For each broken link warning:
1. Check if the target file exists at a different path (use Glob to search)
2. If found, update the link to the correct path
3. If the link is a placeholder (e.g., `path/to/file`), leave it alone
4. If in `working_docs/`, consider if the file is stale and should be deleted

### Undefined Citations (auto-fix)
For each undefined citation:
1. Search `refs/` for the paper (e.g., `refs/*/summary.md` might have the key)
2. If the paper exists, add entry to `refs/references.bib`
3. If the paper doesn't exist, note it for manual addition

### Versioned Files (auto-fix)
For files like `foo_v2.py`:
1. Check if both versions exist
2. If v2 is newer and v1 is unused, delete v1 and rename v2 to base name
3. If both are used, consolidate into one file

### PDF Freshness (auto-fix with --fix flag)
Run `./scripts/check_consistency.sh --fix` to rebuild outdated PDFs.

## Step 4: Report Fixes

After fixing, re-run checks to verify:
```bash
./scripts/check_consistency.sh
```

Report what was fixed and what remains.

## Automated Checks Detail

**Shell-based** (`check_consistency.sh`):
- PDFs newer than LaTeX sources
- Julia scripts have metadata headers
- No versioned source files (*_v1.py, etc)
- VERIFICATION.md exists for subprojects
- Lean sorry count

**Python semantic** (`semantic_checks.py`):
1. **Broken links** - Markdown/LaTeX internal links that don't resolve
2. **Citation validation** - `\cite{}` keys exist in `refs/references.bib`
3. **VERIFICATION.md freshness** - Scripts modified after verification date
4. **Lock staleness** - Expired `.agent.lock` files
5. **TODO/DONE consistency** - Completed tasks reference existing files
6. **History recency** - Agent work logs updated recently
7. **Orphan files** - Source files not referenced anywhere

## LLM-Based Semantic Checks

After automated checks, perform these deeper analyses:

### 1. Code-Theory Correspondence
For each entry in verification campaign tasks:
- Read the source file (e.g., `*/src/*.jl`)
- Read the reference LaTeX (e.g., `latex/*.tex` or `*/docs/*.tex`)
- Compare:
  - Index ordering conventions
  - Normalization factors
  - Sign conventions
  - Loop ordering in contractions

Flag discrepancies as issues.

### 2. Documentation Drift
Compare each subproject's `README.md` or `notes.md` against actual file structure:
- Does the documented structure match `ls -la`?
- Are all documented functions actually implemented?
- Are deprecated features still documented?

### 3. Cross-Reference Validation
Check that claims in one file are supported by evidence in another:
- `VERIFICATION.md` claims "tests pass" -> verify test file exists and runs
- `history/*.md` claims "implemented X" -> verify X exists
- `DONE/*.md` claims "completed" -> verify acceptance criteria met

### 4. Physics Consistency
For numerical code, spot-check:
- Critical exponents match literature values
- Partition functions satisfy duality relations
- Tensor symmetries are preserved

### 5. Multi-Agent Attribution
Scan `history/*_project_work.md`:
- Look for "We" language (should be "I" or specific agent)
- Verify claimed file modifications against git history
- Flag unattributed work

## Output Format

Produce a structured report:

```markdown
## Consistency Check Report
**Date**: YYYY-MM-DD
**Scope**: [quick|full|...]

### Automated Checks
- OK Broken links: 0 issues
- WARNING Citations: 2 undefined keys
- OK Lock staleness: 0 expired

### LLM Analysis

#### Code-Theory Correspondence
| File | Reference | Status | Notes |
|------|-----------|--------|-------|
| */src/script.jl | docs/script.tex | OK | Indices match |

#### Documentation Drift
- `project/README.md`: 1 undocumented function

#### Attribution Issues
- `history/*_project_work.md:342`: Uses "We" for solo work

### Summary
- **Errors**: 0
- **Warnings**: 3
- **Info**: 5

### Recommended Actions
1. Add citation for `Smith2024` to references.bib
2. Update project README with new functions
3. ...
```

## When to Run

- **Before commits**: Run `quick` scope
- **Weekly**: Run `full` scope
- **After major changes**: Run relevant scope
- **When onboarding**: Run `full` to understand project state

## Integration

Results can be:
1. Printed to console
2. Appended to `logs/consistency_check_YYYYMMDD.md`
3. Used to create TODO items for fixes
