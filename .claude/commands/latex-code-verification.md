# LaTeX-Code Cross-Verification

Cross-check LaTeX documentation against code implementations to ensure consistency.

## Usage

```
/latex-code-verification <latex_file> [code_files...]
```

Examples:
- `/latex-code-verification docs/theory.tex`
- `/latex-code-verification paper.tex src/Main.lean src/Defs.lean`

## Instructions

### Step 1: Parse LaTeX for Formulas

Extract mathematical content from the LaTeX file:

1. **Equations**: `\begin{equation}...\end{equation}`, `$$...$$`, `\[...\]`
2. **Definitions**: `\begin{definition}...\end{definition}`
3. **Theorems**: `\begin{theorem}...\end{theorem}`, `\begin{lemma}...`
4. **Inline math**: `$...$`

For each formula, record:
- Label (if any): `\label{eq:xyz}`
- Content
- Line number in LaTeX

### Step 2: Identify Corresponding Code

Search the codebase for implementations:

```bash
# For Lean
grep -rn "def <name>\|theorem <name>\|lemma <name>" **/*.lean

# For Julia
grep -rn "function <name>\|struct <name>" **/*.jl

# For Python
grep -rn "def <name>\|class <name>" **/*.py
```

### Step 3: Compare Implementations

For each formula-code pair:

1. **Type signature match**: Does the code type match the math?
2. **Variable names**: Are they consistent or mapped?
3. **Assumptions**: Are preconditions in the code?
4. **Edge cases**: Does code handle what math assumes away?

### Step 4: Generate Report

```markdown
# LaTeX-Code Verification Report

**LaTeX file:** <file>
**Code files:** <files>
**Date:** <date>

## Summary

| Status | Count |
|--------|-------|
| Matched | <N> |
| Mismatched | <M> |
| Missing in code | <K> |
| Missing in LaTeX | <L> |

## Matched Formulas

### <Label or Description>

**LaTeX** (line <N>):
```latex
<formula>
```

**Code** (<file>:<line>):
```lean
<implementation>
```

**Status:** Match

## Mismatches

### <Label or Description>

**LaTeX** (line <N>):
```latex
<formula>
```

**Code** (<file>:<line>):
```lean
<implementation>
```

**Issue:** <description of mismatch>

**Recommendation:** <how to fix>

## Missing Implementations

| LaTeX Formula | Label | Line | Notes |
|--------------|-------|------|-------|
| <formula> | <label> | <line> | <notes> |

## Missing Documentation

| Code Definition | File:Line | Notes |
|----------------|-----------|-------|
| <name> | <file:line> | <notes> |
```

### Step 5: Consistency Checks

Verify notation consistency:

1. **Symbol mapping**: Create table of LaTeX symbols -> code names
2. **Convention alignment**: Same conventions for indices, etc.
3. **Unit handling**: Are units consistent?

### Step 6: Output

Save report to `docs/verification_report.md` or similar.

## Language-Specific Notes

### Lean
- Check type universes match mathematical levels
- Verify typeclass constraints match assumptions
- Look for `sorry` indicating incomplete proofs

### Julia
- Check numeric types (Float64 vs BigFloat vs symbolic)
- Verify broadcasting conventions
- Look for approximations vs exact formulas

### Python
- Check numpy/scipy function choices
- Verify numerical stability considerations
- Look for precision loss

## Notes

- This is for consistency checking, not proof verification
- Flag any approximations or simplifications in code
- Document intentional deviations with rationale
