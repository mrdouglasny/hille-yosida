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

noncomputable section

open MeasureTheory

/-- A function `f : ℝ → ℝ` is completely monotone on `[0, ∞)` if it is
continuous and all forward differences alternate in sign:
`∑_{k=0}^{n} (-1)^k C(n,k) f(t + kh) ≥ 0` for all `n, t ≥ 0, h > 0`.

For n=0: f(t) ≥ 0. For n=1: f(t) - f(t+h) ≥ 0 (non-increasing).
For n=2: f(t) - 2f(t+h) + f(t+2h) ≥ 0 (convex). Etc.

The standard definition `(-1)^n f^{(n)}(t) ≥ 0` translates to this
forward difference condition. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧
  ∀ (n : ℕ) (t : ℝ) (h : ℝ), 0 ≤ t → 0 < h →
    0 ≤ Finset.sum (Finset.range (n + 1)) fun k =>
      (-1 : ℝ) ^ k * (n.choose k : ℝ) * f (t + k * h)

/-- **Bernstein's theorem** (1928).

A function `f : [0, ∞) → ℝ` is completely monotone if and only if it is
the Laplace transform of a finite positive measure on `[0, ∞)`:

  `f(t) = ∫₀^∞ e^{-tp} dμ(p)`  for all `t ≥ 0`.

Finiteness follows from `f(0) = μ([0,∞)) < ∞`.

Ref: Bernstein (1928); Widder, "The Laplace Transform" Ch. IV. -/
axiom bernstein_theorem (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      μ (Set.Iio 0) = 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        f t = ∫ p, Real.exp (-(t * p)) ∂μ

end
