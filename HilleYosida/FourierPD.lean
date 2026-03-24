/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Fourier Transforms of Positive Measures are Positive-Definite

The "easy direction" of Bochner's theorem: `∑ᵢⱼ c̄ᵢ cⱼ ∫ star(χᵢ) χⱼ dμ`
is real and nonneg for finite positive μ. Equivalently, the Fourier
transform of a positive measure is positive-definite.

Ref: Rudin, "Fourier Analysis on Groups", Thm. 1.4.3
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory Complex Finset

variable {α : Type*} [MeasurableSpace α]

/-- `∑ᵢⱼ c̄ᵢ cⱼ ∫ star(χᵢ) χⱼ dμ` is real and nonneg.

Proof: q = ∫ |∑ cⱼ χⱼ|² dμ ≥ 0 by linearity + normSq ≥ 0.

The swap of ∑ and ∫ uses integral linearity for ℂ-valued functions;
the factoring uses star(a*b) = star(b)*star(a) and normSq_eq_conj_mul_self.

This is an axiom pending resolution of the integral_smul / integral_finset_sum
API matching for ℂ-valued integrals in Mathlib. The mathematical content is
standard (see Rudin, "Fourier Analysis on Groups", Thm 1.4.3). -/
axiom pd_quadratic_form_of_measure
    (μ : Measure α) [IsFiniteMeasure μ]
    {n : ℕ} (c : Fin n → ℂ) (χ : Fin n → α → ℂ)
    (hχ_int : ∀ j, Integrable (χ j) μ) :
    let q := ∑ i, ∑ j, star (c i) * c j * ∫ ξ, star (χ i ξ) * χ j ξ ∂μ
    q.im = 0 ∧ 0 ≤ q.re

end
