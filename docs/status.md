# Hille-Yosida Project Status

**Date:** 2026-03-20
**Branch:** main (clean)
**Lean:** v4.28.0 | **Mathlib:** v4.28.0
**Build:** passing (2495 jobs)

---

## Summary

| Metric | Count |
|--------|-------|
| Source files | 2 |
| Total lines | ~700 |
| Definitions/structures | 6 |
| Theorems proved | 7 |
| Sorries remaining | 6 |

---

## Proved

### Structures & Definitions

[SC]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean
[SGE]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/SemigroupGroupExtension.lean

| Declaration | File | Line | Description |
|-------------|------|------|-------------|
| `StronglyContinuousSemigroup` | [StronglyContinuousSemigroup.lean][SC] | [64][SC-64] | C₀-semigroup: `S(0) = Id`, `S(s+t) = S(s) ∘ S(t)`, strong continuity at 0 |
| `ContractingSemigroup` | [StronglyContinuousSemigroup.lean][SC] | [77][SC-77] | Extends C₀-semigroup with `‖S(t)‖ ≤ 1` |
| `generator` | [StronglyContinuousSemigroup.lean][SC] | [312][SC-312] | Generator domain predicate: `lim_{t→0⁺} (S(t)x - x)/t` exists |
| `domain` | [StronglyContinuousSemigroup.lean][SC] | [324][SC-324] | Generator domain as `Submodule ℝ X` (closed under +, ·) |
| `generatorMap` | [StronglyContinuousSemigroup.lean][SC] | [362][SC-362] | Generator `A : domain →ₗ[ℝ] X` via `Classical.choose` |
| `HasGrowthBound` | [StronglyContinuousSemigroup.lean][SC] | [460][SC-460] | `1 ≤ M ∧ ∀ t ≥ 0, ‖S(t)‖ ≤ M e^{ωt}` |
| `IsSemigroupGroupPD` | [SemigroupGroupExtension.lean][SGE] | [46][SGE-46] | PD condition on `[0,∞) × ℝ^d` with involution `(t,a)* = (t,-a)` |

[SC-64]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L64
[SC-77]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L77
[SC-312]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L312
[SC-324]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L324
[SC-362]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L362
[SC-460]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L460
[SGE-46]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/SemigroupGroupExtension.lean#L46

### Theorems

| Theorem | File | Line | Statement |
|---------|------|------|-----------|
| `operatorZeroApply` | [StronglyContinuousSemigroup.lean][SC] | [87][SC-87] | `S(0) x = x` (pointwise) |
| `normBoundedOnUnitInterval` | [StronglyContinuousSemigroup.lean][SC] | [97][SC-97] | `∃ M ≥ 1, ∀ t ∈ [0,1], ‖S(t)‖ ≤ M` — via **Banach-Steinhaus** |
| `normBoundedOnInterval` | [StronglyContinuousSemigroup.lean][SC] | [172][SC-172] | `∀ n : ℕ, ∃ C > 0, ∀ t ∈ [0,n], ‖S(t)‖ ≤ C` — induction on `n` |
| `strongContAt` | [StronglyContinuousSemigroup.lean][SC] | [211][SC-211] | Strong continuity at every `t₀ ≥ 0` (not just 0) |
| `domain` (submodule) | [StronglyContinuousSemigroup.lean][SC] | [324][SC-324] | `add_mem'`, `zero_mem'`, `smul_mem'` — limits algebra |
| `generatorMap` (linearity) | [StronglyContinuousSemigroup.lean][SC] | [362][SC-362] | `map_add'`, `map_smul'` — via `tendsto_nhds_unique` |
| `existsGrowthBound` | [StronglyContinuousSemigroup.lean][SC] | [467][SC-467] | `∃ ω M, ‖S(t)‖ ≤ M e^{ωt}` — floor decomposition + exp/log |

[SC-87]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L87
[SC-97]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L97
[SC-172]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L172
[SC-211]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L211
[SC-467]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L467

---

## Sorries (6 remaining)

### Resolvent cluster (4) — blocked on Bochner integral

| Declaration | File | Line | Type | Blocker |
|-------------|------|------|------|---------|
| `resolvent` | [StronglyContinuousSemigroup.lean][SC] | [410][SC-410] | `def` | Needs pointwise Bochner integral `R(λ)x = ∫₀^∞ e^{-λt} S(t)x dt` |
| `resolventMapsToDomain` | [StronglyContinuousSemigroup.lean][SC] | [420][SC-420] | theorem | Depends on `resolvent` |
| `resolventRightInv` | [StronglyContinuousSemigroup.lean][SC] | [428][SC-428] | theorem | `(λI - A) R(λ) x = x`; depends on `resolvent` |
| `hilleYosidaResolventBound` | [StronglyContinuousSemigroup.lean][SC] | [449][SC-449] | theorem | `‖R(λ)‖ ≤ 1/λ` for contractions; depends on `resolvent` |

[SC-410]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L410
[SC-420]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L420
[SC-428]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L428
[SC-449]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/StronglyContinuousSemigroup.lean#L449

### BCR Bochner theorem (2) — deep analytic results

| Declaration | File | Line | Type | Blocker |
|-------------|------|------|------|---------|
| `semigroupGroupBochner` | [SemigroupGroupExtension.lean][SGE] | [66][SGE-66] | theorem | BCR Thm 4.1.13: Laplace representation of PD functions |
| `semigroupGroupBochnerExtension` | [SemigroupGroupExtension.lean][SGE] | [111][SGE-111] | theorem | Group extension: Fourier representation for all `t ∈ ℝ` |

[SGE-66]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/SemigroupGroupExtension.lean#L66
[SGE-111]: https://github.com/mrdouglasny/hille-yosida/blob/main/HilleYosida/SemigroupGroupExtension.lean#L111

---

## Dependency Graph

```
normBoundedOnUnitInterval  (Banach-Steinhaus)
  └─► normBoundedOnInterval  (induction on ℕ)
       └─► strongContAt
  └─► existsGrowthBound  (floor decomposition)

resolvent  [SORRY - Bochner integral]
  ├─► resolventMapsToDomain  [SORRY]
  ├─► resolventRightInv  [SORRY]
  └─► hilleYosidaResolventBound  [SORRY]

semigroupGroupBochner  [SORRY - BCR 4.1.13]
  └─► semigroupGroupBochnerExtension  [SORRY]
```

---

## Key Design Decisions

- **Pointwise integrals only**: The resolvent is defined via `x ↦ ∫ e^{-λt} S(t)x dt`, not as an operator-valued integral. This avoids needing strong measurability of `t ↦ S(t)` in the operator norm topology (which fails for general C₀-semigroups).

- **Real scalars**: Everything is over `ℝ`, not `ℂ`. The full QFT extension to unitary groups `e^{itH}` requires complex Hilbert spaces + Stone's theorem (not in Mathlib).

- **G ≠ F**: The group extension `G` uses a Fourier kernel `e^{itp}`, while `F` uses a Laplace kernel `e^{-tp}`. They are related by analytic continuation `t ↦ -it`, not pointwise equality.

---

## Imports

```
StronglyContinuousSemigroup.lean
  ├── Mathlib.Topology.Algebra.Module.Basic
  ├── Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
  ├── Mathlib.Analysis.Normed.Operator.BanachSteinhaus   ← NEW (for normBoundedOnUnitInterval)
  ├── Mathlib.Analysis.SpecialFunctions.Log.Basic
  └── Mathlib.Analysis.SpecialFunctions.ExpDeriv

SemigroupGroupExtension.lean
  ├── HilleYosida.StronglyContinuousSemigroup
  ├── Mathlib.MeasureTheory.Integral.Bochner.Basic
  └── Mathlib.Analysis.InnerProductSpace.Basic
```

---

## Next Steps

1. **Define the resolvent** via pointwise Bochner integral — unblocks 4 sorries
2. **Prove resolvent properties** — `resolventMapsToDomain`, `resolventRightInv`, `hilleYosidaResolventBound`
3. **BCR theorem** — requires substantial measure-theoretic machinery (Fourier-Laplace transforms, support conditions)
4. **Future**: Stone's theorem for complex Hilbert space extension to unitary groups
