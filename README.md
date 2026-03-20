# Hille-Yosida

A Lean 4 formalization of strongly continuous semigroups, the Hille-Yosida resolvent bound, and the semigroup-to-group extension via the BCR Bochner theorem.

## Goal

Prove the `semigroupGroup_bochner` axiom from [OSreconstruction](https://github.com/xiyin137/OSreconstruction), which provides the Fourier-Laplace measure representation for bounded continuous positive-definite functions on `[0,∞) × ℝ^d`. This is the analytical bridge between Euclidean contraction semigroups and Lorentzian unitary groups in QFT.

## Structure

[SC]: HilleYosida/StronglyContinuousSemigroup.lean
[SGE]: HilleYosida/SemigroupGroupExtension.lean

| File | Content | Status |
|------|---------|--------|
| [`StronglyContinuousSemigroup.lean`][SC] | C₀-semigroups, generators, resolvent | Defs proved, resolvent/bounds sorry |
| [`SemigroupGroupExtension.lean`][SGE] | BCR Theorem 4.1.13, group extension | Statements, sorry |

## What is proved

- [`StronglyContinuousSemigroup`][SC-64]: definition with semigroup law + strong continuity
- [`ContractingSemigroup`][SC-77]: contraction semigroups (`‖S(t)‖ ≤ 1`)
- [`operatorZeroApply`][SC-87]: `S(0) x = x`
- [`normBoundedOnUnitInterval`][SC-97]: `‖S(t)‖` bounded on `[0,1]` via Banach-Steinhaus
- [`strongContAt`][SC-211]: strong continuity at every `t₀ ≥ 0`
- [`domain`][SC-324]: generator domain as a `Submodule ℝ X` (algebraic closure proved)
- [`generatorMap`][SC-362]: generator as `LinearMap` from domain to X (linearity proved via `tendsto_nhds_unique`)
- [`normBoundedOnInterval`][SC-172]: norm bound on `[0, n]` by induction
- [`existsGrowthBound`][SC-467]: every C₀-semigroup has exponential growth bound `M e^{ωt}`

[SC-64]: HilleYosida/StronglyContinuousSemigroup.lean#L64
[SC-77]: HilleYosida/StronglyContinuousSemigroup.lean#L77
[SC-87]: HilleYosida/StronglyContinuousSemigroup.lean#L87
[SC-97]: HilleYosida/StronglyContinuousSemigroup.lean#L97
[SC-172]: HilleYosida/StronglyContinuousSemigroup.lean#L172
[SC-211]: HilleYosida/StronglyContinuousSemigroup.lean#L211
[SC-324]: HilleYosida/StronglyContinuousSemigroup.lean#L324
[SC-362]: HilleYosida/StronglyContinuousSemigroup.lean#L362
[SC-467]: HilleYosida/StronglyContinuousSemigroup.lean#L467

## What is stated (sorry)

- [`resolvent`][SC-410]: Laplace transform `R(λ) = ∫₀^∞ e^{-λt} S(t) dt` (needs Bochner integral)
- [`hilleYosidaResolventBound`][SC-449]: `‖R(λ)‖ ≤ 1/λ` (forward direction only)
- [`semigroupGroupBochner`][SGE-66]: BCR Theorem 4.1.13 (the main target)
- [`semigroupGroupBochnerExtension`][SGE-111]: group extension with Fourier formula + PD

[SC-410]: HilleYosida/StronglyContinuousSemigroup.lean#L410
[SC-449]: HilleYosida/StronglyContinuousSemigroup.lean#L449
[SGE-66]: HilleYosida/SemigroupGroupExtension.lean#L66
[SGE-111]: HilleYosida/SemigroupGroupExtension.lean#L111

## Mathematical content

1. **C₀-semigroups**: `S(t)` for `t ≥ 0` with `S(0) = Id`, `S(s+t) = S(s)S(t)`, strong continuity
2. **Hille-Yosida resolvent bound**: contraction semigroup → `‖R(λ)‖ ≤ 1/λ` (forward direction)
3. **BCR Theorem 4.1.13**: bounded continuous PD functions on `[0,∞) × ℝ^d` have Fourier-Laplace measure representations, enabling semigroup-to-group extension
4. **Spectral extension** (QFT): contraction semigroup with H ≥ 0 → unitary group (needs Stone's theorem)

## References

- Hille, "Functional Analysis and Semi-Groups" (1948)
- Yosida, "On the differentiability..." (1948)
- Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), Theorem 4.1.13
- Reed-Simon I-II (1972-1975)
- Engel-Nagel, "One-Parameter Semigroups for Linear Evolution Equations" (2000)
