# Hille-Yosida Project Status

**Date:** 2026-03-21
**Branch:** main (clean)
**Lean:** v4.28.0 | **Mathlib:** v4.28.0
**Build:** passing

---

## Summary

| Metric | Count |
|--------|-------|
| Source files | 2 |
| Total lines | ~620 |
| Definitions/structures | 7 |
| Theorems proved | 10 |
| Sorries remaining | **4** |

---

## Proved

### C₀-semigroup foundations ([EN] Ch. I §5)

| Theorem | Ref | Description |
|---------|-----|-------------|
| `StronglyContinuousSemigroup` | [EN] Def. I.5.1 | C₀-semigroup structure |
| `ContractingSemigroup` | [EN] Def. I.5.6 | Contraction semigroups (`‖S(t)‖ ≤ 1`) |
| `operatorZeroApply` | — | `S(0) x = x` (pointwise) |
| `normBoundedOnUnitInterval` | [EN] Prop. I.5.3 | `∃ M ≥ 1, ∀ t ∈ [0,1], ‖S(t)‖ ≤ M` via Banach-Steinhaus |
| `normBoundedOnInterval` | — | `∀ n : ℕ, ∃ C > 0, ∀ t ∈ [0,n], ‖S(t)‖ ≤ C` |
| `strongContAt` | [EN] Prop. I.5.3 | Strong continuity at every `t₀ ≥ 0` |
| `existsGrowthBound` | [EN] Prop. I.5.5 | `∃ ω M, ‖S(t)‖ ≤ M e^{ωt}` |

### Generator theory ([EN] Ch. II §1)

| Theorem | Ref | Description |
|---------|-----|-------------|
| `domain` | [EN] Def. II.1.2 | Generator domain as `Submodule ℝ X` |
| `generatorMap` | [EN] Def. II.1.2 | Generator `A` as `LinearMap` |

### Resolvent and Hille-Yosida ([EN] Thm. II.1.10)

| Theorem | Ref | Description |
|---------|-----|-------------|
| `integrable_resolvent_integrand` | — | Integrability of `e^{-λt} S(t)x` on `(0,∞)` |
| `ContractingSemigroup.resolvent` | [EN] eq. II.(1.14) | `R(λ)x = ∫₀^∞ e^{-λt} S(t)x dt` — **sorry-free** |
| `hilleYosidaResolventBound` | [EN] Thm. II.1.10(iii) | `‖R(λ)‖ ≤ 1/λ` for contractions |

---

## Sorries (4 remaining)

### Resolvent-generator interface (2) — integral shift trick

These two sorries are deeply entangled and require the same computation
([EN] Thm. II.1.10(i) proof, p. 56; [Linares] eq. 0.15):

| Sorry | Ref | Key Mathlib lemmas needed |
|-------|-----|--------------------------|
| `resolventMapsToDomain` | [EN] Thm. II.1.10(i) | `ContinuousLinearMap.integral_comp_comm`, `integral_comp_add_right`, `integral_hasDerivAt_of_tendsto_ae_right` |
| `resolventRightInv` | [EN] eq. II.(0.16) | Same computation + `tendsto_nhds_unique` |

### BCR Bochner theorem (2)

| Sorry | Ref |
|-------|-----|
| `semigroupGroupBochner` | BCR Thm. 4.1.13 |
| `semigroupGroupBochnerExtension` | BCR extension |

---

## Dependency Graph

```
normBoundedOnUnitInterval  (Banach-Steinhaus)          ✓
  └─► normBoundedOnInterval  (induction on ℕ)         ✓
       └─► strongContAt                               ✓
  └─► existsGrowthBound  (floor decomposition)        ✓

integrable_resolvent_integrand  (contraction + exp)    ✓
  └─► resolvent  (LinearMap.mkContinuous, sorry-free)  ✓
       ├─► hilleYosidaResolventBound  (mkContinuous_norm_le)  ✓
       ├─► resolventMapsToDomain  [SORRY - integral shift]
       └─► resolventRightInv  [SORRY - integral shift]

semigroupGroupBochner  [SORRY - BCR 4.1.13]
  └─► semigroupGroupBochnerExtension  [SORRY]
```

---

## References

- **[EN]** Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  GTM 194, Springer (2000). Primary reference.
- **[Linares]** F. Linares, "The Hille-Yosida Theorem", IMPA lecture notes (2021).
- **[Baudoin]** F. Baudoin, "Semigroups in Banach spaces", lecture notes (2019).
