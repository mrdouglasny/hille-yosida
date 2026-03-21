# Hille-Yosida

A Lean 4 formalization of strongly continuous semigroups, the Hille-Yosida resolvent bound, and the semigroup-to-group extension via the BCR Bochner theorem.

## Goal

Prove the `semigroupGroup_bochner` axiom from [OSreconstruction](https://github.com/xiyin137/OSreconstruction), which provides the Fourier-Laplace measure representation for bounded continuous positive-definite functions on `[0,∞) × ℝ^d`. This is the analytical bridge between Euclidean contraction semigroups and Lorentzian unitary groups in QFT.

## Structure

[SC]: HilleYosida/StronglyContinuousSemigroup.lean
[SGE]: HilleYosida/SemigroupGroupExtension.lean

| File | Content | Status |
|------|---------|--------|
| [`StronglyContinuousSemigroup.lean`][SC] | C₀-semigroups, generators, resolvent, Hille-Yosida | Resolvent proved, 2 sorries |
| [`SemigroupGroupExtension.lean`][SGE] | BCR Theorem 4.1.13, group extension | Statements only, 2 sorries |

## What is proved

### C₀-semigroup foundations ([Linares] Defs. 1-2, Thms. 1-2)
- [`StronglyContinuousSemigroup`][SC-69]: definition with semigroup law + strong continuity
- [`ContractingSemigroup`][SC-82]: contraction semigroups (`‖S(t)‖ ≤ 1`)
- [`operatorZeroApply`][SC-97]: `S(0) x = x`
- [`normBoundedOnUnitInterval`][SC-103]: `‖S(t)‖` bounded on `[0,1]` via Banach-Steinhaus
- [`strongContAt`][SC-220]: strong continuity at every `t₀ ≥ 0` ([Linares] Cor. 1)
- [`existsGrowthBound`][SC-487]: `‖S(t)‖ ≤ M e^{ωt}` ([Linares] Thm. 1, eq. 0.3)

### Generator theory ([Linares] Def. 2, Cor. 2)
- [`domain`][SC-334]: generator domain as `Submodule ℝ X` (algebraic closure proved)
- [`generatorMap`][SC-372]: generator `A` as `LinearMap` (linearity via `tendsto_nhds_unique`)

### Resolvent and Hille-Yosida ([Linares] eq. 0.13-0.14, Thm. 6)
- [`ContractingSemigroup.resolvent`][SC-462]: `R(λ)x = ∫₀^∞ e^{-λt} S(t)x dt` — sorry-free!
  - Integrability via contraction bound + exponential decay
  - Linearity (`map_add'`, `map_smul'`) via `integral_add`, `integral_smul`
  - Operator norm `‖R(λ)‖ ≤ 1/λ` via `norm_integral_le_of_norm_le` + substitution
- [`hilleYosidaResolventBound`][SC-567]: `‖R(λ)‖ ≤ 1/λ` via `LinearMap.mkContinuous_norm_le`

[SC-69]: HilleYosida/StronglyContinuousSemigroup.lean#L69
[SC-82]: HilleYosida/StronglyContinuousSemigroup.lean#L82
[SC-97]: HilleYosida/StronglyContinuousSemigroup.lean#L97
[SC-103]: HilleYosida/StronglyContinuousSemigroup.lean#L103
[SC-220]: HilleYosida/StronglyContinuousSemigroup.lean#L220
[SC-334]: HilleYosida/StronglyContinuousSemigroup.lean#L334
[SC-372]: HilleYosida/StronglyContinuousSemigroup.lean#L372
[SC-462]: HilleYosida/StronglyContinuousSemigroup.lean#L462
[SC-487]: HilleYosida/StronglyContinuousSemigroup.lean#L487
[SC-567]: HilleYosida/StronglyContinuousSemigroup.lean#L567

## What is stated (4 sorries)

- [`resolventMapsToDomain`][SC-550]: `R(λ)x ∈ D(A)` ([Linares] eq. 0.15)
- [`resolventRightInv`][SC-564]: `(λI - A)R(λ) = I` ([Linares] eq. 0.16)
- [`semigroupGroupBochner`][SGE-66]: BCR Theorem 4.1.13 (the main target)
- [`semigroupGroupBochnerExtension`][SGE-111]: group extension with Fourier formula + PD

[SC-550]: HilleYosida/StronglyContinuousSemigroup.lean#L550
[SC-564]: HilleYosida/StronglyContinuousSemigroup.lean#L564
[SGE-66]: HilleYosida/SemigroupGroupExtension.lean#L66
[SGE-111]: HilleYosida/SemigroupGroupExtension.lean#L111

## Mathematical content

1. **C₀-semigroups**: `S(t)` for `t ≥ 0` with `S(0) = Id`, `S(s+t) = S(s)S(t)`, strong continuity
2. **Infinitesimal generator**: `Ax = lim_{t→0⁺} (S(t)x - x)/t` on dense domain `D(A)`
3. **Resolvent**: `R(λ)x = ∫₀^∞ e^{-λt} S(t)x dt` — bounded operator with `‖R(λ)‖ ≤ 1/λ`
4. **Hille-Yosida** (forward): contraction semigroup → `(0,∞) ⊂ ρ(A)` and `‖R(λ)‖ ≤ 1/λ`
5. **BCR Theorem 4.1.13**: bounded continuous PD functions on `[0,∞) × ℝ^d` have Fourier-Laplace measure representations, enabling semigroup-to-group extension

## References

- [Linares] F. Linares, "The Hille-Yosida Theorem", IMPA lecture notes (2021)
- [Baudoin] F. Baudoin, "Semigroups in Banach spaces", lecture notes (2019)
- Hille, "Functional Analysis and Semi-Groups" (1948)
- Yosida, "On the differentiability..." (1948)
- Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), Theorem 4.1.13
- Reed-Simon I-II (1972-1975)
- Engel-Nagel, "One-Parameter Semigroups for Linear Evolution Equations" (2000)
