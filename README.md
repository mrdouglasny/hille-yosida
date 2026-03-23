# Hille-Yosida

A Lean 4 formalization of strongly continuous semigroups, the Hille-Yosida resolvent bound, and the semigroup-to-group extension via the BCR Bochner theorem.

## The Theorem

Let {S(t)} be a **contraction semigroup** on a Banach space X: a family of bounded linear operators satisfying S(0) = I, S(s+t) = S(s)S(t) for s, t >= 0, S(t)x -> x as t -> 0+ for each x, and ||S(t)|| <= 1.

**Hille-Yosida (forward direction).** For every lambda > 0, the resolvent

R(lambda)x = integral from 0 to infinity of e^{-lambda t} S(t)x dt

is a bounded linear operator satisfying:

1. R(lambda) maps X into the domain D(A) of the infinitesimal generator
2. (lambda I - A) R(lambda) = I (the resolvent is the inverse of lambda I - A)
3. ||R(lambda)|| <= 1/lambda

See the [proof outline](docs/proof-outline.md) for an informal summary of the proof.

## Structure

| File | Contents | Sorries |
|------|----------|---------|
| [`StronglyContinuousSemigroup.lean`][SC] | [C0-semigroups, generators, resolvent, Hille-Yosida](summary/HilleYosida/StronglyContinuousSemigroup.md) | **0** |
| [`SemigroupGroupExtension.lean`][SGE] | [BCR Theorem 4.1.13, group extension](summary/HilleYosida/SemigroupGroupExtension.md) | 2 |

[SC]: HilleYosida/StronglyContinuousSemigroup.lean
[SGE]: HilleYosida/SemigroupGroupExtension.lean

## What is proved (sorry-free)

### C0-semigroup foundations
- [`StronglyContinuousSemigroup`][SC-97]: definition with semigroup law + strong continuity
- [`ContractingSemigroup`][SC-111]: contraction semigroups (||S(t)|| <= 1)
- [`normBoundedOnUnitInterval`][SC-133]: uniform operator norm bound on [0,1] via Banach-Steinhaus
- [`strongContAt`][SC-249]: strong continuity at every t_0 >= 0
- [`existsGrowthBound`][SC-820]: every C0-semigroup has exponential growth M*e^{omega*t}

### Generator theory
- [`domain`][SC-363]: generator domain as Submodule (closed under +, scalar mult)
- [`generatorMap`][SC-401]: generator A as LinearMap (linearity via `tendsto_nhds_unique`)

### Resolvent and Hille-Yosida
- [`resolvent`][SC-493]: R(lambda) via Bochner integral — completely sorry-free
- [`resolventMapsToDomain`][SC-746]: R(lambda)x in D(A) via integral shift trick
- [`resolventRightInv`][SC-765]: (lambda I - A) R(lambda) = I
- [`hilleYosidaResolventBound`][SC-800]: ||R(lambda)|| <= 1/lambda

[SC-97]: HilleYosida/StronglyContinuousSemigroup.lean#L97
[SC-111]: HilleYosida/StronglyContinuousSemigroup.lean#L111
[SC-133]: HilleYosida/StronglyContinuousSemigroup.lean#L133
[SC-249]: HilleYosida/StronglyContinuousSemigroup.lean#L249
[SC-363]: HilleYosida/StronglyContinuousSemigroup.lean#L363
[SC-401]: HilleYosida/StronglyContinuousSemigroup.lean#L401
[SC-493]: HilleYosida/StronglyContinuousSemigroup.lean#L493
[SC-746]: HilleYosida/StronglyContinuousSemigroup.lean#L746
[SC-765]: HilleYosida/StronglyContinuousSemigroup.lean#L765
[SC-800]: HilleYosida/StronglyContinuousSemigroup.lean#L800
[SC-820]: HilleYosida/StronglyContinuousSemigroup.lean#L820

## What is stated (2 sorries — BCR axioms)

These require Choquet's theorem and completely monotone function theory, not available in Mathlib. Mathematical correctness verified by Gemini Deep Think.

- [`semigroupGroupBochner`][SGE-66]: BCR Theorem 4.1.13 — Laplace representation of PD functions
- [`semigroupGroupBochnerExtension`][SGE-116]: Group extension with Fourier formula + PD

[SGE-66]: HilleYosida/SemigroupGroupExtension.lean#L66
[SGE-116]: HilleYosida/SemigroupGroupExtension.lean#L116

## Goal

Prove the `semigroupGroup_bochner` axiom from [OSreconstruction](https://github.com/xiyin137/OSreconstruction), which provides the Fourier-Laplace measure representation for bounded continuous positive-definite functions on [0, infinity) x R^d. This is the analytical bridge between Euclidean contraction semigroups and Lorentzian unitary groups in QFT.

## References

- [EN] Engel-Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, GTM 194 (2000)
- [Linares] F. Linares, "The Hille-Yosida Theorem", IMPA lecture notes (2021)
- [Baudoin] F. Baudoin, "Semigroups in Banach spaces", lecture notes (2019)
- Berg-Christensen-Ressel, *Harmonic Analysis on Semigroups* (1984), Theorem 4.1.13
- Hille, *Functional Analysis and Semi-Groups* (1948)
- Yosida, "On the differentiability..." (1948)
- Reed-Simon I-II (1972-1975)
