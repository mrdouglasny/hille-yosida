/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bernstein's Theorem — Axiom

Completely monotone functions on `[0, ∞)` are Laplace transforms of
finite positive measures. This is a key ingredient in the BCR
decomposition: BCR 4.1.13 = Bochner on ℝ^d + Bernstein on [0,∞).

Ref: Bernstein (1928); Widder, "The Laplace Transform" Ch. IV.
Verified correct by Gemini (2026-03-23).
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section

open MeasureTheory

/-- A function `f : ℝ → ℝ` is completely monotone on `[0, ∞)` if it is
C^∞ on `[0, ∞)` and `(-1)^n f^{(n)}(t) ≥ 0` for all `n ∈ ℕ, t ≥ 0`.

This is Widder's definition ("The Laplace Transform", p. 145). It is
equivalent to the forward-difference characterization
`∑_{k=0}^n (-1)^k C(n,k) f(t+kh) ≥ 0`, but the smooth version avoids
a ~500-line bootstrap from differences to derivatives in Lean.

Examples: constants ≥ 0, `e^{-αt}` (α ≥ 0), `1/(t+α)^β` (α,β > 0). -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ f (Set.Ici 0) ∧
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
    0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Set.Ici 0) t

/-! ## Basic properties of CM functions -/

/-- A CM function is nonneg (n=0 case). -/
lemma IsCompletelyMonotone.nonneg (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  have := hcm.2 0 t ht
  simp [iteratedDerivWithin_zero] at this
  exact this

/-- A CM function is non-increasing on [0, ∞) (n=1 case gives f' ≤ 0). -/
lemma IsCompletelyMonotone.deriv_nonpos (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Set.Ici 0) t ≤ 0 := by
  have := hcm.2 1 t ht
  simp only [pow_one] at this
  linarith

/-- A CM function is bounded by f(0) on [0, ∞). -/
lemma IsCompletelyMonotone.bounded (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    f t ≤ f 0 := by
  -- f is non-increasing: f' ≤ 0 on [0,∞) and f is C^∞, so f(t) ≤ f(0).
  -- This follows from the mean value theorem.
  sorry

/-- The n-th derivative of a CM function is also CM (with sign (-1)^n). -/
lemma IsCompletelyMonotone.deriv_cm (hcm : IsCompletelyMonotone f) :
    IsCompletelyMonotone (fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t) := by
  sorry

/-! ## Bernstein's Theorem -/

/-- **Bernstein's theorem** (1928).

A function `f : [0, ∞) → ℝ` is completely monotone if and only if it is
the Laplace transform of a finite positive measure on `[0, ∞)`:

  `f(t) = ∫₀^∞ e^{-tp} dμ(p)`  for all `t ≥ 0`.

Proof strategy (Chafaï 2013, corrected by Gemini review):
1. Taylor remainder: `f(x) = ∫ (1-x/t)_+^{n-1} dσ_n(t)` where
   `dσ_n(t) = (-1)^n/(n-1)! t^{n-1} f^{(n)}(t) dt` (positive by CM)
2. Pushforward: `p = (n-1)/t` gives kernel `(1-xp/(n-1))^{n-1} → e^{-xp}`
3. Total variation: `|σ̃_n| = f(0) - f(∞)` (uniform bound)
4. Prokhorov: extract weakly convergent subsequence `σ̃_{n_k} → μ`
5. Uniform convergence `φ_n → e^{-x}` + Portmanteau → `f(x) = ∫ e^{-xp} dμ(p)`

Ref: Bernstein (1928); Widder, "The Laplace Transform" Ch. IV;
Chafaï (2013) blog post. -/
-- TODO: Replace this axiom with a proof following Chafaï (2013).
-- The proof has 5 phases (see docs/plan-bernstein.md):
-- Phase 2: Taylor remainder with σ_n (integration by parts)
-- Phase 2b: Pushforward p = (n-1)/t
-- Phase 3: Total variation bound |σ̃_n| = f(0) - f(∞)
-- Phase 4: Prokhorov/Helly weak limit
-- Phase 5: Uniform φ_n → e^{-x} + Portmanteau verification
-- Estimated: ~150 lines remaining once Phase 1 helpers are done.
axiom bernstein_theorem (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      μ (Set.Iio 0) = 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        f t = ∫ p, Real.exp (-(t * p)) ∂μ

end
