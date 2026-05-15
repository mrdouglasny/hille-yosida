# Cleanup Notes — `mathlib-ready-cleanup` branch

Running record of the mathlib-readiness cleanup pass. Branch: `mathlib-ready-cleanup` (off `folder-reorg`, off `main`). All commits below preserve `lake build` green.

## Done

### `13452a0` — header-format sweep
Mechanical: copyright block trimmed, descriptive text moved verbatim into post-imports `/-! -/` module docstrings, across 11 files. Per `~/Documents/GitHub/mathlib-ready/docs/style_rules.md` file-structure rules.

### `4a21410` — `@[ext]` lemmas + duplicate-set fix
- Added `StronglyContinuousSemigroup.ext` and `ContractingSemigroup.ext` (extensionality via the `operator` / parent field; remaining structure fields are Prop and so propositionally irrelevant).
- Removed duplicate `set Rlx := …` / `set f := …` lines (lines 592–593 of pre-refactor `BCR_General` era) in `resolvent_generator_tendsto`. Benign in Lean but dead code.

### `b6f3a35` — snake_case rename + `CoeFun`
Eight `Prop`-valued theorems in `Semigroup/StronglyContinuous.lean` renamed from camelCase to snake_case per Mathlib convention (six public, two private). README's Downstream Migration Notes updated with the rename table. `CoeFun (StronglyContinuousSemigroup X) …` instance added so `S t x` works in addition to `S.operator t x`.

### `303128c` — `HasDerivWithinAt` refactor + Generator API redesign
Architectural refactor for **Mathlib API compatibility** (Gemini deep-think recommendation):
- Eliminated `StronglyContinuousSemigroup.generator (x : X) : Prop` predicate.
- `StronglyContinuousSemigroup.generatorMap` renamed to `StronglyContinuousSemigroup.generator` (textbook A = generator).
- `S.domain.carrier` redefined as `{ x | ∃ Ax, HasDerivWithinAt (fun t => S.operator t x) Ax (Set.Ici 0) 0 }`.
- Bridge lemma `hasDerivWithinAt_iff_tendsto_zero` provided for callers wanting the `Tendsto` form.
- Side-effect: `add_mem'`/`zero_mem'`/`smul_mem'` proofs collapsed from ~12 to ~6 lines using `hAx.add` / `hasDerivWithinAt_const` / `hAx.const_smul`.

## Deferred — judgment-heavy items per file

### `Semigroup/GeneratorDerivative.lean`
- **Unused `[CompleteSpace X]` typeclass.** Lean lint suggests `omit [CompleteSpace X]` on both theorems or restructuring the `variable` declaration. Verify mathematical independence from `CompleteSpace` before dropping (per Joseph Myers's Zulip caveat on assumption-weakening — convenience-only hypotheses are fine to keep).
- **Duplicated proof block.** `semigroup_generator_comm` reproduces the `heq`/`h_target` machinery already proved in `semigroup_maps_domain`. Golf candidate; needs careful refactor since both proofs now go through the `HasDerivWithinAt`-bridge.
- **Internal namespace shortening.** `semigroup_maps_domain` and `semigroup_generator_comm` live inside `namespace StronglyContinuousSemigroup`, so the full path already prefixes them — the `semigroup_` prefix in the names is redundant. Could rename to `maps_domain`, `generator_comm` (public API change).

### `Semigroup/StronglyContinuous.lean`
- **`resolvent_generator_tendsto` retained in `Tendsto` form internally.** Public boundary (`resolvent_mapsTo_domain`, `resolvent_right_inv`) bridges to `HasDerivWithinAt`. Less invasive than rewriting the ~160-line resolvent proof, but for full `HasDerivWithinAt`-native consistency it could be migrated.
- **`1/t` vs `t⁻¹` style.** Mathlib's slope uses `t⁻¹`; this file mixes the two. Mechanical pass via `one_div`.

### `Bernstein/*`, `BCR/*`, `Future/*`
- **Not yet audited against `mathlib-ready/docs/lean_methodology/`.** Same audit shape as `Semigroup/StronglyContinuous.lean` likely applies: scan for camelCase Prop names, missing `@[ext]` on structures, opportunities to use Mathlib's existing calculus/measure API instead of bespoke `Tendsto`/`Integrable` constructions.
- **Big files worth checking for natural splits.** `BernsteinChafai.lean` 1660 lines, `BCR/Existence.lean` 2373 lines. Both have section markers (`/-! ## … -/`) inside; whether they correspond to natural file-split seams needs inspection.

### Cross-cutting
- **`generator` (the new operator) — should it be `@[simp]`-tagged for routine unfolding?** Decision deferred until call-site usage stabilizes.
- **API-completeness companions.** Each structure could plausibly gain `_injective`/`_inj` lemmas; not urgent.
- **`HasGrowthBound` (`Has`-prefix).** Mathlib precedent allows `Has` for "has the property of" semantics; kept. Re-check if Mathlib reviewers flag.

### `Bernstein/Basic.lean` (212 lines)
- **Top-level helpers `coe_top_ne_zero`, `nat_le_coe_top`, `nat_lt_coe_top`.** These wrap `WithTop ℕ∞` casts. Strong upstream-Mathlib candidates — propose for `Mathlib.Order.WithTop` directly rather than keeping locally.
- **`iteratedDerivWithin_Icc_eq_Ici`** bridges `Set.Icc` to `Set.Ici` derivative-within transfer. Likely a missing Mathlib lemma; check `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas` and upstream if absent.
- **`IsCompletelyMonotone` definition** — check whether Mathlib already has this under another name (`AbsolutelyMonotone` exists in `mathlib-ready/lean/MathlibReady/`); coordinate before upstreaming.

### `Bernstein/Measures.lean` (500 lines)
- **Bespoke `Tendsto` chains (16 refs)** in `cm_measure_finite_mass` and packaging proofs. Audit whether `MeasureTheory.tendsto_*` lemmas cover the patterns; some may be Mathlib-API-shaped.
- **`cm_density`, `cm_measure`, `cm_rescaled` defs** — strong candidates for extraction as standalone Mathlib API (`Mathlib.MeasureTheory.Measure.CompletelyMonotone`?).

### `Bernstein/Chafai.lean` (1662 lines)
- **Borderline-large file with 36 `Tendsto` refs**; consider whether a natural seam exists (e.g., split off `chafai_repeated_ibp` / `prokhorov_*` machinery).
- **`prob_seq_compact`** and **`tail_setIntegral_tendsto_zero`** — generic-shape lemmas (compact-set-of-probability-measures, tail-integral-vanishing) that look like missing Mathlib infra rather than Chafai-specific.
- **`normalize_le`** — tiny private lemma; check if covered by existing Mathlib `Measure.normalize` lemmas.

### `Bernstein/Theorem.lean` (134 lines)
- File is mostly a re-export and the wrapper `cm_prokhorov_and_verify`, `cm_laplace_representation`, `bernstein_theorem`. Naming is already snake_case; no safe fixes.
- **`bernstein_theorem` itself is the extractable Mathlib PR target.** Statement + dependencies are self-contained.

### `BCR/d0.lean` (1513 lines)
- **`forwardDiff` / `iterForwardDiff` defs** are project-local but the API around them (forward-difference operator, Vandermonde identity, alternating-difference characterization of CM) is generic; consider whether to extract a `Mathlib.Analysis.SpecialFunctions.ForwardDifference` module.
- **`Mollifier` structure** is local; Mathlib has `ContDiffBump` which can produce mollifiers — the file already uses it inside `mollifier_exists`. Consider whether `Mollifier` should be a thin wrapper around `ContDiffBump` or be eliminated entirely in favor of `ContDiffBump` API.
- **`smooth_discrete_cm_implies_cm`** — the bootstrap from discrete forward-difference CM to smooth CM. Pure analysis, no semigroup content; extraction candidate.

### `BCR/Common.lean` (509 lines)
- **Most content is uniqueness-toolkit private to BCR.** Limited upstream relevance.
- **`laplace_measure_unique`** — finite-measure Laplace-transform uniqueness on `[0,∞)`. Could be a Mathlib lemma; check `Mathlib.MeasureTheory.Constructions.LaplaceTransform`.
- **`fourier_uniqueness_finite_measure`** — already uses Mathlib's `Measure.ext_of_charFun`; thin wrapper.

### `BCR/Existence.lean` (2373 lines — BORDERLINE-LARGE)
- **File-split candidate.** Section markers (`Step 1 / 2 / 3`) suggest natural seams: `Existence/SpatialBochner.lean` (Step 1), `Existence/TemporalDecomposition.lean` (Step 2), `Existence/ProductAssembly.lean` (Step 3). 11 `Tendsto` refs concentrated in the assembly step.
- **`gridVec` / `gridCube` / `gridStep` infrastructure** is generic measure-theory plumbing (lattice approximation of measures on `ℝ^d`). Likely a Mathlib gap — possible standalone extraction.
- **`jointApproxMeasure_*` lemmas (10+)** read like Mathlib-API for joint-measure construction from marginals. Extraction candidate.

### `BCR/Uniqueness.lean` (290 lines)
- **`weightedSpatial_eq_of_laplace_fourier_eq` (private)** — abbreviation `weightedSpatial` for `weightedSpatialMeasure` is conventional but borderline; could rename to use the full def name for clarity. Not urgent.

### `BCR/SemigroupGroupDefs.lean` (28 lines)
- **`IsSemigroupGroupPD`** is a `def` returning `Prop`. Convention question: should this be a `Prop` class (`class IsSemigroupGroupPD`)? Mathlib pattern for "positive-definite" / similar predicates is mixed. Defer.

### `BCR/FourierPD.lean` (74 lines)
- **`pd_quadratic_form_of_measure`** is the only theorem; uses Mathlib `Measure` API directly. Clean. No deferred items beyond style polish (`1/h` → `h⁻¹` etc.).

### `BCR/SemigroupGroupExtension.lean` (272 lines)
- **Main public theorems** `semigroup_group_bochner` and `semigroup_group_bochner_extension` are the project-payload; specific to OS-axiom application. Not natural Mathlib extraction candidates by themselves (too research-specific).
- **`semigroup_group_bochner_extension`** could be golfed via `semigroup_group_bochner`; the README already notes the delegation.

### `Future/GenerationTheorem.lean` (113 lines, axiomatized)
- **`DenseLinearOperator` structure** has a `domain →ₗ[ℝ] X` field whose type depends on `domain`, so an `@[ext]` lemma needs `HEq` handling. Skipped from this pass; non-trivial.
- **Axioms `domain_isDense` and `hilleYosidaGeneration`** are intentional out-of-chain debt. Each needs a Gemini deep-think axiom-vetting pass before further use (per `~/.claude/CLAUDE.md` axiom rules); not addressed here.

### Repo-wide
- **No deprecated Mathlib names found** (greped for `Set.left_mem_*`, similar). Clean.
- **No dead private lemmas found** via reference counting on this pass.

## Downstream impact recap

OSreconstruction (`OSReconstruction/SCV/SemigroupGroupBochner.lean`) has three categories of changes pending after this branch lands:
1. **Module paths.** Old `HilleYosida.SemigroupGroupExtension` / `HilleYosida.BCR_General` → `HilleYosida.BCR.SemigroupGroupExtension` / `HilleYosida.BCR.General` (or just `HilleYosida.BCR` pillar).
2. **Theorem renames.** Any usage of `operatorZeroApply`, `strongContAt`, `resolventMapsToDomain`, `resolventRightInv`, `hilleYosidaResolventBound`, `existsGrowthBound`.
3. **Generator API.** `S.generator x : Prop` → `x ∈ S.domain`; `S.generatorMap` → `S.generator`.

All three are documented in `README.md` → "Downstream Migration Notes".

## Catalog regen pending

After merging `folder-reorg` / `mathlib-ready-cleanup`:
```
cd ~/Documents/GitHub/catalogs
./gen_catalog.sh ~/Documents/GitHub/hille-yosida hille-yosida
./build_index.sh
```
