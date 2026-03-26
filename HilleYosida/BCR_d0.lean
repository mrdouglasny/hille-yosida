/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# BCR Theorem 4.1.13 for d=0: PD on semigroup [0,∞) → Laplace transform

A bounded continuous function `f : [0,∞) → ℝ` satisfying the semigroup
positive-definite condition
  `∑ᵢⱼ c̄ᵢ cⱼ f(tᵢ+tⱼ) ≥ 0`
for all `tᵢ ≥ 0`, `cᵢ ∈ ℂ`, is the Laplace transform of a finite
positive measure on `[0,∞)`.

Proof route:
  PD →(forward differences)→ CM-discrete →(smoothness)→ CM →(Bernstein)→ Laplace

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), §4.2
* Widder, "The Laplace Transform" (1941), Ch. IV
-/

import HilleYosida.Bernstein
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section

open MeasureTheory Complex Finset Set

/-! ## Semigroup PD condition for scalar functions -/

/-- PD on the additive semigroup [0,∞): `∑ c̄ᵢ cⱼ f(tᵢ+tⱼ) ≥ 0` for all
finite systems of points `tᵢ ≥ 0` and coefficients `cᵢ ∈ ℂ`. -/
def IsSemigroupPD (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ),
    (∀ i, 0 ≤ ts i) →
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j * (f (ts i + ts j) : ℂ)).re

/-! ## Basic properties of semigroup PD functions -/

/-- `f(0) ≥ 0` (n=1, c=[1], t=[0]). -/
lemma IsSemigroupPD.nonneg_zero (hpd : IsSemigroupPD f) : 0 ≤ f 0 := by
  have h := hpd 1 ![1] ![0] (by intro i; fin_cases i; simp)
  simp [Fin.sum_univ_one, Matrix.cons_val_zero, star_one, one_mul, add_zero] at h
  exact_mod_cast h

/-- `|f(t)| ≤ f(0)` for all `t ≥ 0` (Cauchy-Schwarz for PD). -/
lemma IsSemigroupPD.abs_le (hpd : IsSemigroupPD f) (t : ℝ) (ht : 0 ≤ t) :
    |f t| ≤ f 0 := by
  -- From PD with n=2, c=[1, z], ts=[0, t] for |z|=1 chosen so zf(t) = |f(t)|
  -- we get f(0) + z̄f(t) + zf(t) + f(0) ≥ 0, i.e., 2f(0) + 2Re(zf(t)) ≥ 0.
  -- Choosing z = -sgn(f(t)) gives 2f(0) - 2|f(t)| ≥ 0.
  by_cases hft : f t = 0
  · simp [hft, hpd.nonneg_zero]
  have h := hpd 2 ![1, -1] ![0, t] (by intro i; fin_cases i <;> simp [ht])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero,
    Fin.val_one, star_one, one_mul, star_neg, neg_mul, add_zero, zero_add] at h
  -- h : 0 ≤ (f 0 - f t - f t + f (t + t) : ℂ).re
  -- Need a different choice. Use c = [1, eiθ] with θ chosen to make f(t)eiθ = -|f(t)|
  sorry

/-! ## Forward differences and the CM-discrete condition

The key insight: the PD condition with specific test vectors gives
`(-1)^n Δ_h^n f(t) ≥ 0` where `Δ_h` is the forward difference operator.

This is the discrete/finite-difference version of complete monotonicity. -/

/-- Forward difference operator: `Δ_h f(t) = f(t+h) - f(t)`. -/
def forwardDiff (h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (t + h) - f t

/-- Iterated forward difference: `Δ_h^n f(t) = ∑_{k=0}^n (-1)^{n-k} C(n,k) f(t+kh)`. -/
def iterForwardDiff : ℕ → ℝ → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, f, t => f t
  | n+1, h, f, t => iterForwardDiff n h (forwardDiff h f) t

/-- Explicit formula: `Δ_h^n f(t) = ∑_{k=0}^n (-1)^{n-k} C(n,k) f(t+kh)`. -/
lemma iterForwardDiff_eq_sum (n : ℕ) (h : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    iterForwardDiff n h f t =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * f (t + k * h) := by
  induction n generalizing f t with
  | zero => simp [iterForwardDiff]
  | succ n ih =>
    -- iterForwardDiff (n+1) h f t = iterForwardDiff n h (forwardDiff h f) t
    simp only [iterForwardDiff]
    rw [ih]
    simp only [forwardDiff]
    -- Now we have ∑ k in range(n+1), (-1)^(n-k) * C(n,k) * (f(t+k*h+h) - f(t+k*h))
    -- Need to show this equals ∑ k in range(n+2), (-1)^(n+1-k) * C(n+1,k) * f(t+k*h)
    -- Split the difference
    simp only [mul_sub, Finset.sum_sub_distrib]
    -- Rewrite as two sums and use Pascal's identity
    sorry

/-- **PD → alternating forward differences.**
For `f` semigroup-PD, `h > 0`, `t ≥ 0`:
  `(-1)^n Δ_h^n f(t) ≥ 0`

Proof: Choose `c_k = (-1)^k √C(n,k)` in the PD quadratic form.
Then `∑ᵢⱼ c̄ᵢ cⱼ f(tᵢ+tⱼ)` with `tₖ = t/2 + kh/2` gives
  `∑ᵢⱼ (-1)^{i+j} C(n,i)^{1/2} C(n,j)^{1/2} f(t + (i+j)h/2)`
which after grouping by `i+j = m` gives `(-1)^n Δ_{h/2}^n f(t)` ... no,
this needs more care with the convolution identity.

**Alternative approach** (BCR Prop. 4.2.2): Use the identity
  `(-1)^n Δ_h^n f(t) = ∑ᵢⱼ c̄ᵢ cⱼ f(sᵢ + sⱼ)`
where `c_k = (-1)^k √C(n,k)`, `s_k = t/2 + k·h`.
The PD condition gives `0 ≤ ∑ c̄ᵢcⱼ f(sᵢ+sⱼ)`.

We verify: `sᵢ + sⱼ = t + (i+j)h` and
`∑ᵢⱼ (-1)^{i+j} C(n,i)^{1/2} C(n,j)^{1/2} f(t+(i+j)h)`
= `∑_m (∑_{i+j=m} (-1)^m C(n,i)^{1/2} C(n,j)^{1/2}) f(t+mh)`
= `∑_m (-1)^m C(2n, m)^{?} f(t+mh)` ... this doesn't simplify cleanly.

**Correct approach** (Widder IV.12): Use `n+1` points with
`c_k = (-1)^k C(n,k)` (integer, not square root!) and `s_k = t/2 + k·h/2`.
Then `s_i + s_j = t + (i+j)·h/2` and the sum becomes a **convolution square**
of the binomial coefficients, which equals `(-1)^n` times the n-th forward
difference, by the Vandermonde identity. -/
lemma IsSemigroupPD.alternating_forwardDiff (hpd : IsSemigroupPD f)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (h : ℝ) (hh : 0 < h) :
    0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h f t := by
  sorry

/-! ## CM-discrete → CM (smoothness)

A continuous function with nonneg alternating forward differences is C^∞
and its derivatives have the correct signs. This is Widder IV, Thm 12a.

The proof uses:
1. Alternating differences → f is monotone decreasing (n=1)
2. Alternating differences → (-Δ_h f)/h is bounded and monotone → f' exists
3. Iterate to get all derivatives -/

/-- **BCR d=0**: Bounded continuous semigroup-PD → completely monotone.

This is the key lemma that reduces the general BCR to Bernstein. -/
theorem IsSemigroupPD.isCompletelyMonotone
    (hpd : IsSemigroupPD f) (hcont : ContinuousOn f (Ici 0))
    (hbdd : ∃ C : ℝ, ∀ t, 0 ≤ t → |f t| ≤ C) :
    IsCompletelyMonotone f := by
  -- The alternating forward differences are nonneg:
  have hdiff := hpd.alternating_forwardDiff
  -- From this + continuity, we derive C^∞ smoothness and the sign conditions.
  -- The smoothness argument (Widder IV.12a) proceeds by induction on derivative order:
  --   nonneg alternating Δ_h^1 → f monotone decreasing → f' ≤ 0 exists
  --   nonneg alternating Δ_h^2 → f' monotone increasing → f'' ≥ 0 exists
  --   ...
  sorry

/-! ## Main theorem: BCR 4.1.13 for d=0 -/

/-- **BCR 4.1.13 (d=0)**: A bounded continuous semigroup-PD function on [0,∞)
is the Laplace transform of a finite positive measure supported on [0,∞).

Combines `IsSemigroupPD.isCompletelyMonotone` with `bernstein_theorem`. -/
theorem semigroup_pd_laplace (f : ℝ → ℝ)
    (hpd : IsSemigroupPD f) (hcont : ContinuousOn f (Ici 0))
    (hbdd : ∃ C : ℝ, ∀ t, 0 ≤ t → |f t| ≤ C) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
      μ (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  exact bernstein_theorem f (hpd.isCompletelyMonotone hcont hbdd)

end
