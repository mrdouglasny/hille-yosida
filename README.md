# Hille-Yosida

A Lean 4 formalization of strongly continuous semigroups, the Hille-Yosida resolvent bound, and the semigroup-to-group extension via the BCR Bochner theorem.

## Goal

Prove the `semigroupGroup_bochner` axiom from [OSreconstruction](https://github.com/xiyin137/OSreconstruction), which provides the Fourier-Laplace measure representation for bounded continuous positive-definite functions on `[0,∞) × ℝ^d`. This is the analytical bridge between Euclidean contraction semigroups and Lorentzian unitary groups in QFT.

## Structure

| File | Content | Status |
|------|---------|--------|
| `StronglyContinuousSemigroup.lean` | C₀-semigroups, generators, resolvent | Defs proved, resolvent/bounds sorry |
| `SemigroupGroupExtension.lean` | BCR Theorem 4.1.13, group extension | Statements, sorry |

## What is proved

- `StronglyContinuousSemigroup`: definition with semigroup law + strong continuity
- `ContractingSemigroup`: contraction semigroups (`‖S(t)‖ ≤ 1`)
- `operator_zero_apply`: `S(0) x = x`
- `strong_cont_at`: strong continuity at every `t₀ ≥ 0` (modulo `norm_bounded_on_unit_interval`)
- `domain`: generator domain as a `Submodule ℝ X` (algebraic closure proved)
- `generatorMap`: generator as `LinearMap` from domain to X (linearity proved via `tendsto_nhds_unique`)
- `norm_bounded_on_interval`: norm bound on `[0, n]` by induction (modulo unit interval bound)

## What is stated (sorry)

- `norm_bounded_on_unit_interval`: `‖S(t)‖` bounded on `[0,1]` (needs UBP)
- `resolvent`: Laplace transform `R(λ) = ∫₀^∞ e^{-λt} S(t) dt` (needs Bochner integral)
- `hille_yosida_resolvent_bound`: `‖R(λ)‖ ≤ 1/λ` (forward direction only)
- `semigroupGroup_bochner`: BCR Theorem 4.1.13 (the main target)
- `semigroupGroup_bochner_extension`: group extension with Fourier formula + PD
- `semigroup_extends_to_group_of_positive_generator`: spectral extension (needs Stone's theorem)

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
