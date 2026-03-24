/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Fourier Transforms of Positive Measures are Positive-Definite

The "easy direction" of Bochner's theorem: if μ is a finite positive
measure and χⱼ are bounded measurable functions, then the quadratic form
`∑ᵢⱼ c̄ᵢ cⱼ ∫ star(χᵢ) χⱼ dμ` is real and nonneg.

Proof: `q = ∫ |∑ cⱼ χⱼ|² dμ ≥ 0` by linearity + |z|² ≥ 0.

Ref: Rudin, "Fourier Analysis on Groups", Thm. 1.4.3
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory Complex Finset

variable {α : Type*} [MeasurableSpace α]

/-- The quadratic form `∑ᵢⱼ c̄ᵢ cⱼ ∫ star(χᵢ) χⱼ dμ` is real and nonneg.

This is the "easy direction" of Bochner's theorem. The proof uses:
1. Linearity of integral to swap ∑ and ∫
2. `∑ᵢⱼ star(wᵢ) wⱼ = star(∑ w)(∑ w)` (product of sums)
3. `star(z) * z = ↑(normSq z)` which is real and nonneg
4. `∫ (nonneg real) dμ ≥ 0` for a positive measure -/
theorem pd_quadratic_form_of_measure
    (μ : Measure α) [IsFiniteMeasure μ]
    {n : ℕ} (c : Fin n → ℂ) (χ : Fin n → α → ℂ)
    (hχ_int : ∀ j, Integrable (χ j) μ) :
    let q := ∑ i, ∑ j, star (c i) * c j * ∫ ξ, star (χ i ξ) * χ j ξ ∂μ
    q.im = 0 ∧ 0 ≤ q.re := by
  -- q = ∑ᵢⱼ star(cᵢ) cⱼ ∫ star(χᵢ) χⱼ dμ
  -- The proof strategy: show q = ∫ ↑(normSq(∑ cⱼ χⱼ)) dμ, then im=0 ∧ re≥0.
  -- Blocked on: swapping the double sum through the integral requires
  -- integral_smul (to pull star(cᵢ)cⱼ inside) + integral_finset_sum (to swap ∑ and ∫).
  -- Each step needs integrability conditions and careful ℂ algebra.
  -- The mathematical content is: ∫ |∑ cⱼ χⱼ|² dμ ≥ 0.
  exact sorry

end
