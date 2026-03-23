/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bernstein's Theorem and the BCR Decomposition

This file states Bernstein's theorem for completely monotone functions on
`[0, ∞)` and sketches how BCR Theorem 4.1.13 decomposes into:

  **BCR 4.1.13 = Bochner on ℝ^d  +  Bernstein on [0, ∞)**

The Bochner theorem on ℝ^d is fully proved in the companion project
`github.com/mrdouglasny/bochner` (0 sorries). Bernstein's theorem is
stated here as an axiom.

## Mathematical Content

### Bernstein's Theorem (1928)

A function `f : [0, ∞) → ℝ` is **completely monotone** if it is C^∞ and
`(-1)^n f^{(n)}(t) ≥ 0` for all `t > 0` and `n ∈ ℕ`. Equivalently
(Bernstein), `f` is completely monotone iff it is the Laplace transform
of a finite positive measure on `[0, ∞)`:

  `f(t) = ∫₀^∞ e^{-tp} dμ(p)`

### BCR Decomposition

Given a bounded continuous PD function `F(t, a)` on `[0, ∞) × ℝ^d`:

1. **Spatial Fourier part** (Bochner on ℝ^d): For each fixed `t ≥ 0`,
   `a ↦ F(t, a)` is PD on `(ℝ^d, +)`. By Bochner's theorem (proved in
   `mrdouglasny/bochner`), there exists a finite measure `ν_t` on `ℝ^d`
   with `F(t, a) = ∫ e^{i⟨a, q⟩} dν_t(q)`.

2. **Temporal Laplace part** (Bernstein on [0,∞)): The semigroup PD
   condition implies that for each Borel set `B ⊆ ℝ^d`, the function
   `t ↦ ν_t(B)` is completely monotone. By Bernstein's theorem, there
   exists a measure `σ_B` on `[0, ∞)` with
   `ν_t(B) = ∫₀^∞ e^{-tp} dσ_B(p)`.

3. **Product measure**: The family `{σ_B}` defines a measure `μ` on
   `[0, ∞) × ℝ^d` with `F(t, a) = ∫ e^{-tp} e^{i⟨a,q⟩} dμ(p, q)`.

## References

* Bernstein, "Sur les fonctions absolument monotones" (1928)
* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), §4.1
* Widder, "The Laplace Transform" (1941), Ch. IV
-/

import HilleYosida.StronglyContinuousSemigroup

noncomputable section

open MeasureTheory

/-! ## Completely Monotone Functions -/

/-- A function `f : ℝ → ℝ` is completely monotone on `(0, ∞)` if it is
smooth and `(-1)^n f^{(n)}(t) ≥ 0` for all `t > 0` and `n ∈ ℕ`.

For the formal statement, we use the sequential characterization:
`f` is completely monotone iff for all `n ∈ ℕ`, `t > 0`, and `h > 0`,
the `n`-th forward difference `Δ_h^n f(t) := ∑ (-1)^k C(n,k) f(t + kh)`
satisfies `(-1)^n Δ_h^n f(t) ≥ 0`. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧
  ∀ (n : ℕ) (t : ℝ) (h : ℝ), 0 < t → 0 < h →
    0 ≤ (-1 : ℝ) ^ n * (Finset.sum (Finset.range (n + 1)) fun k =>
      (-1 : ℝ) ^ k * (n.choose k : ℝ) * f (t + k * h))

/-! ## Bernstein's Theorem -/

/-- **Bernstein's theorem** (1928).

A function `f : [0, ∞) → ℝ` is completely monotone if and only if it is
the Laplace transform of a finite positive measure on `[0, ∞)`:

  `f(t) = ∫₀^∞ e^{-tp} dμ(p)`  for all `t ≥ 0`.

The forward direction (Laplace transform is CM) is elementary. The
converse uses Widder's inversion formula or the Helly selection theorem
(compactness in the space of measures).

Ref: Bernstein (1928); Widder, "The Laplace Transform" Ch. IV;
[EN] implicit in the proof of Thm. II.3.5 via Yosida approximation. -/
axiom bernstein_theorem (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      μ (Set.Iio 0) = 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        f t = ∫ p, Real.exp (-(t * p)) ∂μ

/-! ## BCR Decomposition Strategy

The following outlines how to combine Bochner + Bernstein → BCR.
When the bochner repo is imported as a dependency, the spatial
Fourier step becomes a theorem invocation. -/

-- NOTE: To complete the BCR proof, this project needs:
-- 1. `require bochner from git "https://github.com/mrdouglasny/bochner.git"`
--    in lakefile.toml (after toolchain alignment to v4.29)
-- 2. Import `Bochner.Main` for `bochner_theorem` and `IsPositiveDefinite`
-- 3. For each fixed t, show a ↦ F(t,a) is IsPositiveDefinite on ℝ^d
--    (from IsSemigroupGroupPD with all ts_i = t/2)
-- 4. Apply bochner_theorem to get the spatial measure ν_t
-- 5. Show t ↦ ν_t(B) is completely monotone (from semigroup PD)
-- 6. Apply bernstein_theorem to get the temporal measure
-- 7. Combine into the product measure on [0,∞) × ℝ^d

end
