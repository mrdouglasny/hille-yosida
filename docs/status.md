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

| Declaration | File | Line | Description |
|-------------|------|------|-------------|
| `StronglyContinuousSemigroup` | StronglyContinuousSemigroup.lean | 64 | C₀-semigroup: `S(0) = Id`, `S(s+t) = S(s) ∘ S(t)`, strong continuity at 0 |
| `ContractingSemigroup` | StronglyContinuousSemigroup.lean | 77 | Extends C₀-semigroup with `‖S(t)‖ ≤ 1` |
| `generator` | StronglyContinuousSemigroup.lean | 312 | Generator domain predicate: `lim_{t→0⁺} (S(t)x - x)/t` exists |
| `domain` | StronglyContinuousSemigroup.lean | 324 | Generator domain as `Submodule ℝ X` (closed under +, ·) |
| `generatorMap` | StronglyContinuousSemigroup.lean | 362 | Generator `A : domain →ₗ[ℝ] X` via `Classical.choose` |
| `HasGrowthBound` | StronglyContinuousSemigroup.lean | 460 | `1 ≤ M ∧ ∀ t ≥ 0, ‖S(t)‖ ≤ M e^{ωt}` |
| `IsSemigroupGroupPD` | SemigroupGroupExtension.lean | 46 | PD condition on `[0,∞) × ℝ^d` with involution `(t,a)* = (t,-a)` |

### Theorems

| Theorem | File | Line | Statement |
|---------|------|------|-----------|
| `operatorZeroApply` | StronglyContinuousSemigroup.lean | 87 | `S(0) x = x` (pointwise) |
| `normBoundedOnUnitInterval` | StronglyContinuousSemigroup.lean | 97 | `∃ M ≥ 1, ∀ t ∈ [0,1], ‖S(t)‖ ≤ M` — via **Banach-Steinhaus** |
| `normBoundedOnInterval` | StronglyContinuousSemigroup.lean | 172 | `∀ n : ℕ, ∃ C > 0, ∀ t ∈ [0,n], ‖S(t)‖ ≤ C` — induction on `n` |
| `strongContAt` | StronglyContinuousSemigroup.lean | 211 | Strong continuity at every `t₀ ≥ 0` (not just 0) |
| `domain` (submodule) | StronglyContinuousSemigroup.lean | 324 | `add_mem'`, `zero_mem'`, `smul_mem'` — limits algebra |
| `generatorMap` (linearity) | StronglyContinuousSemigroup.lean | 362 | `map_add'`, `map_smul'` — via `tendsto_nhds_unique` |
| `existsGrowthBound` | StronglyContinuousSemigroup.lean | 467 | `∃ ω M, ‖S(t)‖ ≤ M e^{ωt}` — floor decomposition + exp/log |

---

## Sorries (6 remaining)

### Resolvent cluster (4) — blocked on Bochner integral

| Declaration | File | Line | Type | Blocker |
|-------------|------|------|------|---------|
| `resolvent` | StronglyContinuousSemigroup.lean | 410 | `def` | Needs pointwise Bochner integral `R(λ)x = ∫₀^∞ e^{-λt} S(t)x dt` |
| `resolventMapsToDomain` | StronglyContinuousSemigroup.lean | 420 | theorem | Depends on `resolvent` |
| `resolventRightInv` | StronglyContinuousSemigroup.lean | 428 | theorem | `(λI - A) R(λ) x = x`; depends on `resolvent` |
| `hilleYosidaResolventBound` | StronglyContinuousSemigroup.lean | 449 | theorem | `‖R(λ)‖ ≤ 1/λ` for contractions; depends on `resolvent` |

### BCR Bochner theorem (2) — deep analytic results

| Declaration | File | Line | Type | Blocker |
|-------------|------|------|------|---------|
| `semigroupGroupBochner` | SemigroupGroupExtension.lean | 66 | theorem | BCR Thm 4.1.13: Laplace representation of PD functions |
| `semigroupGroupBochnerExtension` | SemigroupGroupExtension.lean | 111 | theorem | Group extension: Fourier representation for all `t ∈ ℝ` |

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
