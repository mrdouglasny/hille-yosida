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
import Mathlib.Analysis.Calculus.Taylor

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
  simpa [iteratedDerivWithin_zero] using hcm.2 0 t ht

/-- A CM function is non-increasing on [0, ∞) (n=1 case gives f' ≤ 0). -/
lemma IsCompletelyMonotone.deriv_nonpos (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Set.Ici 0) t ≤ 0 := by
  have := hcm.2 1 t ht
  simp only [pow_one] at this
  linarith

/-- A CM function is bounded by f(0) on [0, ∞). -/
lemma IsCompletelyMonotone.bounded (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    f t ≤ f 0 := by
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := Ne.symm (ne_of_beq_false rfl)
  have hanti : AntitoneOn f (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcm.1.continuousOn
      ((hcm.1.differentiableOn htop).mono interior_subset)
      (fun x hx => by
        rw [interior_Ici] at hx
        have h1 := hcm.deriv_nonpos x (le_of_lt hx)
        rwa [iteratedDerivWithin_one,
          derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at h1)
  exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht

/-- The n-th derivative of a CM function is also CM (with sign (-1)^n). -/
lemma IsCompletelyMonotone.deriv_cm (hcm : IsCompletelyMonotone f) :
    IsCompletelyMonotone (fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t) := by
  sorry

/-! ## Bernstein's Theorem -/

/-- **Bernstein's theorem** (1928). CM ⟹ Laplace transform.

Proof following Chafaï (2013) with Gemini corrections:
1. Taylor remainder gives `f(x) = ∫ (1-x/t)_+^{n-1} dσ_n(t)`
2. Pushforward `p = (n-1)/t` gives kernel `(1-xp/(n-1))^{n-1} → e^{-xp}`
3. Total variation `|σ̃_n| = f(0) - f(∞)` (uniform bound)
4. Prokhorov: extract `σ̃_{n_k} → μ`
5. Uniform `φ_n → e^{-x}` + Portmanteau → `f(x) = ∫ e^{-xp} dμ(p)` -/
theorem bernstein_theorem (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      μ (Set.Iio 0) = 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  -- Define the density for σ_n: ρ_n(t) = (-1)^n/(n-1)! · t^{n-1} · f^{(n)}(t)
  -- This is nonneg by the CM condition.
  set ρ : ℕ → ℝ → ℝ := fun n t =>
    if n = 0 then 0
    else (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Set.Ici 0) t
  -- ρ_n(t) ≥ 0 for t ≥ 0 (from CM condition)
  have hρ_nonneg : ∀ n, ∀ t, 0 ≤ t → 0 ≤ ρ n t := by
    intro n t ht
    simp only [ρ]
    split_ifs with hn
    · exact le_refl 0
    · -- Regroup: (-1)^n/(n-1)! · t^{n-1} · f^{(n)}(t)
      --        = (t^{n-1} / (n-1)!) · ((-1)^n · f^{(n)}(t))
      have hcm_sign := hcm.2 n t ht
      have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
        Nat.cast_pos.mpr (Nat.factorial_pos _)
      have hrw : (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
        iteratedDerivWithin n f (Set.Ici 0) t =
        t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
        ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Set.Ici 0) t) := by
        field_simp
      rw [hrw]
      exact mul_nonneg (div_nonneg (pow_nonneg ht _) (le_of_lt hfact_pos)) hcm_sign
  -- Phase 2-5: Taylor remainder → pushforward → Prokhorov → verify
  -- Each phase is ~30 lines of Lean. The full proof follows Chafaï (2013).
  exact sorry

end
