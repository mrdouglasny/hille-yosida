# Hille-Yosida

A Lean 4 formalization of strongly continuous semigroups, the Hille-Yosida generation theorem, and the semigroup-to-group extension via Bochner's theorem.

## Goal

Prove the `semigroupGroup_bochner` axiom from [OSreconstruction](https://github.com/xiyin137/OSreconstruction), which is the analytical bridge between Euclidean contraction semigroups (`e^{-tH}` for `t > 0`) and Lorentzian unitary groups (`e^{itH}` for `t ∈ ℝ`) in quantum field theory.

## Structure

| File | Content | Status |
|------|---------|--------|
| `StronglyContinuousSemigroup.lean` | C₀-semigroups, generators, Hille-Yosida theorem | Definitions + sorrys |
| `SemigroupGroupExtension.lean` | Semigroup-to-group extension, BCR Theorem 4.1.13 | Definitions + sorrys |

## Mathematical Content

1. **Strongly continuous semigroups** (C₀-semigroups): `S(t)` for `t ≥ 0` with `S(0) = Id`, `S(s+t) = S(s)S(t)`, strong continuity
2. **Hille-Yosida theorem**: characterizes generators of contraction semigroups via resolvent bounds
3. **Semigroup-group Bochner theorem** (BCR 4.1.13): bounded continuous positive-definite functions on `[0,∞) × ℝ^d` have Fourier-Laplace representations, enabling extension from semigroup to group

## References

- Hille, "Functional Analysis and Semi-Groups" (1948)
- Yosida, "On the differentiability and the representation of one-parameter semi-group of linear operators" (1948)
- Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), Theorem 4.1.13
- Reed-Simon, "Methods of Modern Mathematical Physics I-II" (1972-1975)
- Engel-Nagel, "One-Parameter Semigroups for Linear Evolution Equations" (2000)
