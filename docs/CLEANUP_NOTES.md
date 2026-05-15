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
