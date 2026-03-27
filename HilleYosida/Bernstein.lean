/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bernstein's Theorem — Main results

`cm_prokhorov_and_verify`, `cm_laplace_representation`, `bernstein_theorem`.

This file re-exports all definitions and lemmas from the Bernstein module:
- `BernsteinBasic`: `IsCompletelyMonotone`, basic CM properties, Taylor remainder
- `BernsteinMeasures`: `cm_density`, `cm_measure`, IBP, `bernstein_kernel`, rescaling
- `BernsteinChafai`: Chafai identity, Prokhorov extraction, limit identification

Ref: Bernstein (1928); Widder, "The Laplace Transform" Ch. IV.
-/

import HilleYosida.BernsteinChafai

noncomputable section

open MeasureTheory Set intervalIntegral Filter

/-- **Prokhorov extraction + Laplace verification** (Chafaï 2013).

For each `n ≥ 2`, the pushforward `σ̃_n = cm_rescaled f n` has:
- Total mass `≤ f(0) - L` (from `cm_measure_finite_mass`)
- Support on `[0, ∞)` (from `cm_rescaled_Iio_zero`)

The correct Chafaï identity (for each fixed `n` and `x ≥ 0`):

  `f(x) - L = ∫ φ_n(xp) dσ̃_n(p)`

where `φ_n(u) = (1 - u/(n-1))_+^{n-1}`. This follows from the Taylor integral
remainder on `[x, T]` with `T → ∞`, using the boundary term decay
`T^k f^{(k)}(T) → 0` for CM functions (which follows from the integrability
of `(-1)^k f^{(k)}` on `[0, ∞)` and its monotonicity).

NOTE: An earlier decomposition incorrectly stated `∫ φ_n dσ̃_n = f(x) - taylorPoly(n-1, 0, x)`.
This is FALSE: the Bernstein integral is over `(x, ∞)` while the Taylor remainder is over
`(0, x)` — different domains with different kernels.

Given the correct identity, the proof concludes:
1. **Prokhorov** (`isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le`):
   extract `σ̃_{n_k} → μ₀` weakly.
2. **Diagonal convergence**: `∫ φ_{n_k} dσ̃_{n_k} → ∫ e^{-xp} dμ₀` using
   `bernstein_kernel_tendsto` + weak convergence + dominated convergence.
3. **Conclusion**: `f(x) - L = ∫ e^{-xp} dμ₀`. -/
lemma cm_prokhorov_and_verify (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L))
    (hL_nn : 0 ≤ L)
    (hmass : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_measure f n) ∧
      (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L))
    (hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Set.Iio 0) = 0) :
    ∃ (μ₀ : Measure ℝ), IsFiniteMeasure μ₀ ∧ μ₀ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t →
        f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  -- Step 1: cm_rescaled is finite for n ≥ 2
  have hfin_rescaled : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_rescaled f n) := by
    intro n hn; haveI := (hmass n hn).1
    exact cm_rescaled_isFiniteMeasure f n
  -- Step 2: mass bound for rescaled measures
  have hmass_rescaled : ∀ n, 2 ≤ n →
      (cm_rescaled f n) Set.univ ≤ ENNReal.ofReal (f 0 - L) := by
    intro n hn; rw [cm_rescaled_mass_eq]; exact (hmass n hn).2
  -- Step 3: Chafaï identity (proved in chafai_identity, sorry'd there)
  have hchafai : ∀ n, 2 ≤ n → ∀ x, 0 ≤ x →
      f x - L = ∫ p, bernstein_kernel n x p ∂(cm_rescaled f n) :=
    fun n hn x hx => chafai_identity f hcm n hn x hx L hL
  -- Step 4: Prokhorov extraction + limit identification
  exact prokhorov_limit_identification f hcm L hL hL_nn hmass_rescaled hsupp
    hfin_rescaled hchafai

/-- **CM Laplace representation** (Chafaï 2013 argument). For a CM function
`f` with limit `L ≥ 0` at infinity, there exists a finite positive measure
`μ₀` on `[0, ∞)` with `f(t) = L + ∫ e^{-tp} dμ₀(p)`.

The proof factors into sorry-free structural lemmas (support, mass
preservation) and two sorry'd analytic steps:
  1. `cm_measure_finite_mass` — total mass bound from Taylor's formula
  2. `cm_prokhorov_and_verify` — Prokhorov + limit identification

Mathlib tools for resolving the sorry's:
  - `isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le` (Prokhorov)
  - `IsCompact.isSeqCompact` (compact → sequentially compact)
  - `FiniteMeasure.tendsto_iff_forall_integral_tendsto` (weak convergence)
  - `taylor_integral_remainder` (proved above, sorry-free) -/
theorem cm_laplace_representation (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) (hL_nn : 0 ≤ L) :
    ∃ (μ₀ : Measure ℝ), IsFiniteMeasure μ₀ ∧ μ₀ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  have hmass : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_measure f n) ∧
      (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L) :=
    fun n hn => cm_measure_finite_mass f hcm n hn L hL
  have hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Set.Iio 0) = 0 :=
    fun n hn => cm_rescaled_Iio_zero f n hn
  exact cm_prokhorov_and_verify f hcm L hL hL_nn hmass hsupp

/-- **Bernstein's theorem** (1928). Every completely monotone function on `[0, ∞)` is
the Laplace transform of a finite positive measure on `[0, ∞)`.

Proof outline (Chafaï 2013), using `taylor_integral_remainder`:
1. Taylor integral remainder ⟹ `f(x) = boundary(n,T) + ∫_x^T ρ_n(t) dt` (nonneg)
2. Pushforward `p = (n-1)/t` ⟹ kernel `(1-xp/(n-1))^{n-1} → e^{-xp}`
3. Total variation `|σ̃_n| = f(0) - f(∞)` (uniform bound)
4. Prokhorov ⟹ `σ̃_{n_k} → μ` weakly
5. Portmanteau ⟹ `f(x) = ∫ e^{-xp} dμ(p)` -/
theorem bernstein_theorem (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      μ (Set.Iio 0) = 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  -- ═══════════════════════════════════════════════════════════════
  -- Established infrastructure (all sorry-free):
  -- ═══════════════════════════════════════════════════════════════
  -- Step 1: f has a limit L ≥ 0 at infinity
  obtain ⟨L, hL_tendsto, hL_nonneg⟩ := IsCompletelyMonotone.tendsto_atTop hcm
  -- Step 2: -f' is integrable on (0,∞) with total mass f(0) - L
  have hint := IsCompletelyMonotone.neg_deriv_integrableOn hcm hL_tendsto
  have hmass := IsCompletelyMonotone.integral_Ioi_neg_deriv hcm hL_tendsto hint
  -- Step 3: The density ρ_n is nonneg (cm_density_nonneg)
  -- Step 4: The Taylor remainder has definite sign (taylor_nonneg_remainder)
  -- Step 5: f(x) - f(T) = ∫ (-f') dt on each [x,T] (integral_neg_deriv)
  -- ═══════════════════════════════════════════════════════════════
  -- Step 6: Prokhorov + Portmanteau → μ₀ with f = L + ∫ e^{-xp} dμ₀
  -- ═══════════════════════════════════════════════════════════════
  have ⟨μ₀, hfin₀, hsupp₀, hrep⟩ :=
    cm_laplace_representation f hcm L hL_tendsto hL_nonneg
  -- Step 7: Package μ = μ₀ + L·δ₀ (sorry-free)
  exact @bernstein_packaging f L hL_nonneg μ₀ hfin₀ hsupp₀ hrep

end
