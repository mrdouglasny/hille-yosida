# Stock-Take — `mathlib-ready-cleanup` branch (2026-05-15)

A frank assessment of what the cleanup pass actually accomplished, what it didn't, and what's next.

## The headline

The work was a **broad-but-uneven** cleanup. The Semigroup pillar got the full mathlib-ready treatment; the other 12 files got a much lighter pass. The biggest single asset from this branch is not the code changes — it's the *punch list* of judgment-heavy work in `CLEANUP_NOTES.md`, the *workflow* for doing this kind of cleanup on other repos, and the *first-file-deep-clean* as a template.

Calling this "hille-yosida is cleaned up" would be inaccurate. Calling it "we know exactly what cleanup remains, and one pillar is done" is accurate.

## What was done

**Structural** (already on `origin/main` and `origin/folder-reorg` before this branch started):
- `BCR_General.lean` (3096 lines) split into `BCR/Common.lean` + `BCR/Existence.lean` + `BCR/Uniqueness.lean` + a re-export shim. The shared `TemporalSliceRep` toolkit and `fourier_uniqueness_finite_measure` landed in `Common`.
- 14 files moved into `Semigroup/`, `Bernstein/`, `BCR/`, `Future/` subfolders with import-path updates project-wide.
- Three pillar facade files (`HilleYosida/Semigroup.lean`, `HilleYosida/Bernstein.lean`, `HilleYosida/BCR.lean`) added so downstream consumers can stay on stable pillar imports.

**On `mathlib-ready-cleanup`** (6 commits, all pushed to origin):
1. Module docstrings reformatted (copyright trimmed, descriptions moved post-imports) across 11 files.
2. `@[ext]` lemmas + duplicate-set fix in `StronglyContinuous.lean`.
3. snake_case rename pass on 8 `Prop` declarations in `Semigroup/StronglyContinuous.lean` + `CoeFun` instance.
4. **`HasDerivWithinAt` refactor + Generator API redesign** in `Semigroup/StronglyContinuous.lean` — predicate elimination, `generatorMap` → `generator`, domain reformulated via Mathlib's calculus API. Side-effect: algebraic-closure proofs shrank ~12 → ~6 lines each.
5. `docs/CLEANUP_NOTES.md` scaffolding.
6. Bernstein/BCR/Future audit pass — 5 renames, 2 `@[ext]` lemmas, full per-file punch list of judgment-heavy items.

**Documentation:**
- README's "Downstream Migration Notes" section enumerates every public-surface change in three categories (module paths, theorem renames, generator API).
- `docs/CLEANUP_NOTES.md` records per-file deferred items.
- Four cross-project memory files in `~/.claude/projects/.../memory/` capture transferable lessons.

## What was not done

**The Semigroup pillar is the only one that got the deep treatment.** Bernstein and BCR got the safe mechanical pass — header format, a handful of renames, two `@[ext]` lemmas. The substantive work on those pillars (per `CLEANUP_NOTES.md`'s judgment-heavy section) is *flagged*, not *done*. Specifically:

- **No bespoke-`Tendsto`-to-Mathlib-API refactors** outside the Semigroup pillar. `Bernstein/Measures.lean` and `Bernstein/Chafai.lean` together have ~52 `Tendsto` references that should be audited the way `StronglyContinuous.lean`'s were.
- **No file splits.** `BCR/Existence.lean` (2373 lines) has a natural Step 1/2/3 seam; `Bernstein/Chafai.lean` (1662 lines) has a natural Prokhorov/Chafai seam. Neither was split.
- **No `Mollifier` vs `ContDiffBump` decision.** `BCR/d0.lean` defines its own `Mollifier` and also uses Mathlib's `ContDiffBump` — the duplication wasn't resolved.
- **No assumption-weakening pass.** The lint-flagged unused `[CompleteSpace X]` on `GeneratorDerivative.lean` was deferred; no other assumption-weakening was audited.
- **No `IsCompletelyMonotone` ↔ `AbsolutelyMonotone` coordination** with `mathlib-ready/lean/MathlibReady/`.
- **No Mathlib upstream PR** prepared, even though `bernstein_theorem`, the Hille-Yosida resolvent bound, and several helper lemmas are PR-shaped.

**OSreconstruction has three categories of downstream debt** queued up by this branch:
1. Module paths (post-folder-reorg)
2. Theorem renames (snake_case sweep + BCR renames)
3. Generator API switch (predicate elimination, `generatorMap` → `generator`)

The branch can't be merged to `main` without these resolved in OSreconstruction.

**Catalog regen** is pending (per `~/Documents/GitHub/catalogs/` workflow).

## What was learned

Worth pulling forward into future cleanup sessions on osforgff, gaussian-field, pphi2:

1. **Use existing Mathlib calculus/measure APIs over bespoke `Tendsto`/`Integrable`.** This is upstream-acceptance binding, and the algebraic-closure proofs typically get cleaner as a side effect. Captured in memory `feedback_tendsto_to_hasderivwithinat.md`.
2. **Pillar facade files are cheap insurance.** ~3 lines each, immune downstream from internal reshuffling. Captured in memory `feedback_pillar_facade_files.md`.
3. **Split-with-shared-helper is a 3-file pattern, not 2.** Don't fight it. Captured in memory `feedback_split_bundled_existence_uniqueness.md`.
4. **Concrete Mathlib API gaps** worth upstreaming (`HasDerivWithinAt.unique` alias, `iff_tendsto_slope` simp friction). Captured in memory `reference_mathlib_api_gaps.md`.
5. **Branch hygiene.** Splitting structural changes (`folder-reorg`) from per-file polish (`mathlib-ready-cleanup`) made each diff reviewable in isolation; bundling would have been ugly.
6. **Calibration first, then sweep.** Doing one file deeply (`Semigroup/StronglyContinuous.lean`) and then auditing the others uncovered the "safe vs. judgment-heavy" distinction that made the audit pass actually useful instead of a brittle blanket-apply.

## What's next — options ranked

1. **Update OSreconstruction.** Three mechanical changes; unblocks merging `folder-reorg` → `main` and `mathlib-ready-cleanup` → `folder-reorg`. ~30 min.
2. **Mathlib upstream PR for the Hille-Yosida resolvent bound.** The Semigroup pillar is ready; the rest can follow incrementally. Real return on the cleanup investment. Probably 1–2 weeks wall-clock (per the formalization-time-estimates rubric in user-CLAUDE.md, this is a "small sister project" downstream of all our prep work).
3. **Apply the deep Semigroup-pillar methodology to Bernstein and BCR.** Iterate on the punch list in `CLEANUP_NOTES.md`. Highest-value items: the `Tendsto`-chain audit in `Bernstein/Measures.lean` + `Chafai.lean`, the file split on `BCR/Existence.lean`, the `Mollifier`/`ContDiffBump` decision.
4. **Move the same workflow to another repo** (osforgff, gaussian-field) — these are the larger candidates per the Reservoir survey's gap analysis (no upstream competitors for semigroup/spectral/Schwartz/Sobolev material).

The original framing of the conversation was about shouyi for fleet-wide cleanup. The workflow we converged on (audit → safe fixes inline → judgment-heavy in CLEANUP_NOTES.md → punch list per file) is plausibly what shouyi *should* do automated, but we did it manually. If you want shouyi-ified versions of these passes, that's its own project — separate from finishing hille-yosida or starting upstream PRs.
