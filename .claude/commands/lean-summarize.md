---
description: Summarize a Lean 4 source file as informal-math markdown in summary/, listing every definition and theorem in source order with LaTeX statements and proof dependencies
---

# Lean Informal Math Summarizer

Produce an informal-math Markdown summary of a Lean 4 source file.

## Invocation

```
/lean-summarize [path/to/File.lean]
```

If no argument is given, summarize the Lean file most recently discussed or edited in this session.  If the target is ambiguous, ask the user.

## Step-by-step procedure

### 1. Resolve the target file

- Accept `$ARGUMENTS` as the path (absolute or relative to the project root).
- If `$ARGUMENTS` is empty, infer the target from session context (most recently read/edited `.lean` file).

### 2. Compute the output path

Given source path `<dir>/<rest>.lean`, the output is `summary/<dir>/<rest>.md`.

Examples:
- `OSforGFF/OS/OS3_DiagonalRP.lean` → `summary/OSforGFF/OS/OS3_DiagonalRP.md`
- `OSforGFF/Covariance/Position.lean` → `summary/OSforGFF/Covariance/Position.md`

### 3. Staleness check

Run the following to compare timestamps:

```bash
python3 - <<'EOF'
import os, sys
src = "LEAN_FILE_PATH"
out = "SUMMARY_FILE_PATH"
if not os.path.exists(out):
    print("STALE")
elif os.path.getmtime(src) > os.path.getmtime(out):
    print("STALE")
else:
    print("FRESH")
EOF
```

If the result is `FRESH`, report: *"Summary is already up to date: `<output path>`"* and stop.

### 4. Read the Lean source

Use the Read tool to load the full source file.

### 5. Parse declarations in source order

Scan the file top to bottom.  For each top-level declaration, record:

| Kind | Lean keywords |
|------|---------------|
| **Definition** | `def`, `noncomputable def`, `abbrev`, `structure`, `class`, `instance` (if mathematically significant) |
| **Theorem** | `theorem`, `lemma`, `proposition`, `corollary` |

Skip: `import`, `open`, `section`, `namespace`, `variable`, `set_option`, `attribute`, `#check`, `#eval`, `example`.

For section/module doc comments (`/-! ... -/`), capture them as **section headers** in the output.

### 6. For each declaration, produce its summary entry

#### Definitions

```markdown
### `name` — Definition

**Lean signature**
```lean
def name (arg : Type) : ReturnType
```
*(Quote the full signature with all parameters and the return type. Omit the body (everything after `:=`). Never abbreviate parameters with `...` — write them out completely.)*

**Informal**: [One sentence: what mathematical object or concept this defines, with LaTeX for formulas.]
```

#### Theorems / Lemmas

```markdown
### [`name`](<source-link>) — Lemma  *(or Theorem)*

**Statement**: [Informal English sentence with LaTeX inline math, e.g., $\|Θx - x\| = 2\lvert x_0 \rvert$.]

**Proof uses**: [`dep1`](<link>), `dep2`, `dep3`[, and *N* sorry(s)]
```

**How to link declaration names**:
- **Declaration headings**: always link `name` to its source line: `[`name`](path/to/File.lean#LNN)`.
  The path is relative from the `summary/` output file to the project root source file.
- **"Proof uses" entries**: link any dependency that is declared in a project `.lean` file
  (i.e., under `OSforGFF/`). Use the same relative-path format.
  Leave Mathlib names (qualified with e.g. `Real.`, `MeasureTheory.`, `Finset.`) as plain backtick code.
- To find a dependency's file and line, use `grep -rn "lemma NAME\|theorem NAME\|def NAME" OSforGFF/`.

**How to extract proof dependencies**:
- Read the proof body (everything after `:= by` or `:=`).
- Collect every *named identifier* that refers to a previously declared theorem, lemma, or definition — these are the identifiers that appear in positions where a term (not a tactic keyword) is expected.
- **Tactic keywords to ignore** (never list as dependencies): `simp`, `ring`, `abel`, `linarith`, `omega`, `norm_num`, `positivity`, `push_neg`, `rw`, `have`, `let`, `show`, `intro`, `intros`, `apply`, `exact`, `refine`, `obtain`, `use`, `constructor`, `cases`, `rcases`, `ext`, `funext`, `congr`, `conv`, `calc`, `split_ifs`, `split`, `by_cases`, `by_contra`, `decide`, `rfl`, `trivial`, `assumption`, `tauto`, `field_simp`, `gcongr`, `contrapose`, `induction`, `fin_cases`.
- **Omit elementary Mathlib lemmas** that could be discharged by `simp` (e.g., `abs_mul`, `Real.norm_eq_abs`, `Set.mem_Ioi`, `norm_nonneg`). Only list lemmas that carry real mathematical content.
- Count the number of `sorry` keywords in the proof body.
- For `simp [...]` and `rw [...]` calls, *do* list the named lemmas passed as arguments if they carry mathematical content.
- Prefer unqualified short names when the namespace is obvious; use fully qualified names for Mathlib lemmas.
- If there are no named dependencies (pure tactic proof), write: **Proof uses**: *(direct tactic proof)*.

### 7. Generate the Markdown file

Use this template:

```markdown
# `<filename>.lean` — Informal Summary

> **Source**: [`<relative/path/to/file.lean>`](<relative/path/to/file.lean>)
> **Generated**: <current date and time YYYY-MM-DD HH:MM>
> **Note**: Auto-generated by `/lean-summarize`. Re-run to refresh.

## Overview

<2–4 sentences extracted or inferred from the module doc comment (`/-! # ... -/`).
If no module doc, write a brief summary of what the file proves.>

## Status

**Main result**: <"Fully proven" if zero sorries, otherwise "Not yet proven (N sorry(s))">

**Major gaps** *(sorries that directly block the file's primary theorem(s))*:
- `name`: <one-line description of what needs to be proved>
- ...

**Minor gaps** *(sorries in helper lemmas; do not block the main theorem directly)*:
- `name`: <one-line description>
- ...

*(Omit "Major gaps" or "Minor gaps" section if empty. If zero sorries total, replace both with "None — file is sorry-free.")*

**Length**: <N> lines, <D> definition(s) + <T> theorem(s)/lemma(s)

---

<For each section doc comment, emit a `##` header with its title.>

<For each declaration, emit its entry as described in Step 6.>

---

*This file has **N** definitions and **M** theorems/lemmas (<K> with sorry).*
```

**Classifying major vs minor gaps:**
- A sorry is **major** if it appears in the proof of the file's primary result(s) — typically the final `theorem` or any theorem whose name appears in the module doc's "Key results" list.
- A sorry is **major** if a primary theorem *depends transitively* on it (i.e., there is no sorry-free path to the conclusion).
- A sorry is **minor** if it blocks only auxiliary or intermediate lemmas, not the stated main result.

### 8. Write the output

1. Create the `summary/<subdir>/` directory if it does not exist (use `mkdir -p`).
2. Write the generated Markdown using the Write tool.
3. **Update `README.md`**: find the table row whose first cell links to the source file
   (e.g. `| [FileName](OSforGFF/X/FileName.lean) | ... |`) and make the Contents cell a
   link to the new summary:
   - Before: `| [FileName](OSforGFF/X/FileName.lean) | Some description text |`
   - After:  `| [FileName](OSforGFF/X/FileName.lean) | [Some description text](summary/OSforGFF/X/FileName.md) |`
   - If the Contents cell is already a link (from a previous run), leave it unchanged.
   - If no matching row exists in README.md, skip this step silently.
4. Report: *"Written to `summary/<path>.md`"*.

## LaTeX conventions (match the project style)

- **Vector norms**: `$\lVert x \rVert$` (use `\lVert`/`\rVert` everywhere, even outside tables).
- **Absolute value of scalars**: `$\lvert x_0 \rvert$`.
- **Time reflection**: `$\Theta x$` for `QFT.timeReflection x`.
- **Integrals**: `$\int_0^\infty e^{-sm^2} H_s(r)\, ds$`.
- **Inline math** for short expressions, display math (`$$...$$`) for equations that are the main point of a theorem.
- **No `\operatorname`**: GitHub's KaTeX renderer does not support `\operatorname{...}`.
  Use `\mathrm{...}` instead for named operators: `\mathrm{Re}`, `\mathrm{tr}`, `\mathrm{Im}`,
  `\mathrm{ofReal}`, predicate names, etc.
- Follow the LaTeX rules in `.claude/commands/update-docs.md` (Rules 1–4).

## Example output (excerpt)

```markdown
# `OS3_DiagonalRP.lean` — Informal Summary

> **Source**: [`OSforGFF/OS/OS3_DiagonalRP.lean`](OSforGFF/OS/OS3_DiagonalRP.lean)
> **Generated**: 2026-03-03
> **Note**: Auto-generated by `/lean-summarize`. Re-run to refresh.

## Overview

Proves reflection positivity for the free covariance via a diagonal kernel argument,
avoiding the spatial Fourier decomposition. The key steps are: (1) the distance
formula $\lVert \Theta x - x \rVert = 2\lvert x_0 \rvert$, (2) nonnegativity of the
diagonal covariance $C(\Theta x, x) \geq 0$ for positive-time $x$, and (3) existence
of a Euclidean motion normalizing any pair $(x,y)$ to axis form.

---

## Step 1: Component formula and distance

### `timeReflection_sub_self_apply` — Lemma

**Statement**: The $i$-th component of $\Theta x - x$ is $-2x_0$ if $i = 0$, and $0$ otherwise.

**Proof uses**: `WithLp.equiv_symm_apply`, `Function.update_apply`

---

### `timeReflection_sub_self_norm` — Theorem

**Statement**: $\lVert \Theta x - x \rVert = 2\lvert x_0 \rvert$.

**Proof uses**: `timeReflection_sub_self_norm_sq`, `Real.sqrt_sq`, `Real.sqrt_sq_eq_abs`

---

## Step 4: Euclidean normalization to axis form

### `onTimeAxis` — Definition

**Lean signature**
```lean
noncomputable def onTimeAxis (t : ℝ) : SpaceTime
```
**Informal**: The point $(t, 0, 0, 0) \in \mathbb{R}^4$ on the time axis.

---

### `exists_euclidean_to_axis_form` — Theorem

**Statement**: For any $x, y \in \mathbb{R}^4$, there exists a Euclidean motion $g$ and
$t \geq 0$ such that $g(x) = (t, 0, 0, 0)$ and $g(y) = (-t, 0, 0, 0)$.

**Proof uses**: `exists_rotation_map_to_timeAxis`, `onTimeAxis_neg`, `onTimeAxis_add`,
`map_sub`, and *1 sorry*

---

*This file has **5** definitions and **8** theorems/lemmas (2 with sorry).*
```
