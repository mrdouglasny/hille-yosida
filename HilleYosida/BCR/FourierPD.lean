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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open MeasureTheory Complex Finset

variable {α : Type*} [MeasurableSpace α]

/-- `∑ᵢⱼ c̄ᵢ cⱼ ∫ star(χᵢ) χⱼ dμ` is real and nonneg.

Proof: swap sum and integral to get `q = ∫ |∑ cⱼ χⱼ|² dμ`, then use
normSq ≥ 0 and integral_nonneg.

The hypothesis requires integrability of products `star(χᵢ) · χⱼ`, which
is automatic when the χⱼ are bounded (L^∞) or in L². Pure L¹ integrability
is NOT sufficient: if some `|χᵢ|²` is not integrable, the Bochner integral
returns 0 and the matrix `∫ star(χᵢ) χⱼ dμ` can fail to be PSD.

Ref: Rudin, "Fourier Analysis on Groups", Thm 1.4.3. -/
theorem pd_quadratic_form_of_measure
    (μ : Measure α) [IsFiniteMeasure μ]
    {n : ℕ} (c : Fin n → ℂ) (χ : Fin n → α → ℂ)
    (hχ_int : ∀ i j, Integrable (fun ξ => star (χ i ξ) * χ j ξ) μ) :
    let q := ∑ i, ∑ j, star (c i) * c j * ∫ ξ, star (χ i ξ) * χ j ξ ∂μ
    q.im = 0 ∧ 0 ≤ q.re := by
  intro q
  -- Step 1: Swap sums inside the integral
  -- ∫ ∑ᵢ ∑ⱼ ... dμ = ∑ᵢ ∑ⱼ ∫ ... dμ = ∑ᵢ ∑ⱼ star(cᵢ) cⱼ ∫ star(χᵢ)χⱼ dμ = q
  have hpull : q = ∫ ξ, ∑ i, ∑ j,
      star (c i) * c j * (star (χ i ξ) * χ j ξ) ∂μ := by
    symm
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => (hχ_int i j).const_mul _))]
    congr 1; ext i
    rw [integral_finset_sum _ (fun j _ => (hχ_int i j).const_mul _)]
    congr 1; ext j
    exact integral_const_mul _ _
  -- Step 2: Pointwise, the double sum equals normSq(∑ cⱼ χⱼ)
  have hpointwise : ∀ ξ, ∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j * (star (χ i ξ) * χ j ξ) =
      ↑(Complex.normSq (∑ j : Fin n, c j * χ j ξ)) := by
    intro ξ
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul]
    rw [Finset.sum_mul]
    congr 1; ext i
    rw [Finset.mul_sum]
    congr 1; ext j
    simp only [star_def]; ring
  have hrewrite : q = ∫ ξ, ↑(Complex.normSq (∑ j, c j * χ j ξ)) ∂μ := by
    rw [hpull]; congr 1; ext ξ; exact hpointwise ξ
  -- Step 3: ∫ ofReal(normSq) dμ is real and nonneg
  rw [hrewrite, show ∫ ξ, (↑(Complex.normSq (∑ j, c j * χ j ξ)) : ℂ) ∂μ =
    ↑(∫ ξ, Complex.normSq (∑ j, c j * χ j ξ) ∂μ) from integral_ofReal]
  exact ⟨Complex.ofReal_im _, Complex.ofReal_re _ ▸
    integral_nonneg (fun ξ => Complex.normSq_nonneg _)⟩

end
