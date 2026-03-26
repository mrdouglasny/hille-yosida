/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# BCR Theorem 4.1.13: Semigroup Bochner via Spatial Bochner + BCR d=0

Proves `semigroupGroupBochner` (BCR 4.1.13) by decomposing into:
  BCR 4.1.13(d) = Bochner on ℝ^d  +  BCR 4.1.13(d=0) on [0,∞)

The proof uses `semigroup_pd_laplace` (BCR d=0, proved in BCR_d0.lean)
for the temporal decomposition, and `bochner_theorem` (from
mrdouglasny/bochner) for the spatial decomposition.

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), §4.1
* Bernstein, "Sur les fonctions absolument monotones" (1928)
-/

import HilleYosida.SemigroupGroupExtension
import HilleYosida.BCR_d0
import Bochner.Main
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

noncomputable section

open MeasureTheory Complex Set Filter Finset

/-! ## Step 1: Spatial Bochner measures

For each `t ≥ 0`, `spatial_slice_pd` (proved below) gives
`IsPositiveDefinite (a ↦ F(t, a))`. Combined with `bochner_theorem`,
this yields a finite measure ν_t with F(t, a) = ∫ e^{i⟨a,q⟩} dν_t(q). -/

/-- For `t ≥ 0`, the spatial slice `a ↦ F(t, a)` is continuous. -/
lemma spatial_slice_continuous {d : ℕ} {F : ℝ → (Fin d → ℝ) → ℂ}
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (t : ℝ) (ht : 0 ≤ t) : Continuous (fun a => F t a) :=
  hcont.comp_continuous (continuous_const.prodMk continuous_id')
    (fun _ => ⟨mem_Ici.mpr ht, mem_univ _⟩)

/-- The spatial slice `a ↦ F(t, a)` is positive definite (group PD on ℝ^d).

Proved by specializing `IsSemigroupGroupPD` with all times equal to `t/2`:
then `tᵢ + tⱼ = t` and the quadratic form becomes the PD condition for `F(t, ·)`. -/
lemma spatial_slice_pd {d : ℕ} {F : ℝ → (Fin d → ℝ) → ℂ}
    (hpd : IsSemigroupGroupPD d F) (t : ℝ) (ht : 0 ≤ t) :
    IsPositiveDefinite (fun a : Fin d → ℝ => F t a) where
  hermitian := by
    intro x
    -- Need: F(t, -x) = conj(F(t, x))
    -- Strategy: use IsSemigroupGroupPD with n=2, ts=[t/2,t/2], as=[0,x]
    -- with c=[1,1] and c=[1,I] to extract Im and Re conditions.
    --
    -- First show F(t,0) is real
    have h0_im : (F t 0).im = 0 := by
      have h := hpd 1 ![1] ![t / 2] ![0] (by intro i; fin_cases i; simp; linarith)
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, star_one, one_mul,
        add_halves, sub_self] at h
      exact h.1
    -- Use n=2, ts=[t/2,t/2], as=[0,x], c=[1,1] for imaginary part
    have h1 := hpd 2 ![1, 1] ![t / 2, t / 2] ![0, x]
      (by intro i; fin_cases i <;> simp <;> linarith)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      star_one, one_mul, add_halves] at h1
    -- h1.1: Im(F(t,x-0) + F(t,0-x) + F(t,0) + F(t,0)) = 0
    -- i.e., Im(F(t,x)) + Im(F(t,-x)) + 2·Im(F(t,0)) = 0
    -- Since Im(F(t,0)) = 0: Im(F(t,x)) = -Im(F(t,-x))
    -- Use n=2, ts=[t/2,t/2], as=[0,x], c=[1,I] for real part
    have h2 := hpd 2 ![1, I] ![t / 2, t / 2] ![0, x]
      (by intro i; fin_cases i <;> simp <;> linarith)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      star_one, one_mul, add_halves] at h2
    -- h2.1 gives: Im(... involving I * F terms ...) = 0
    -- which extracts Re(F(t,x)) = Re(F(t,-x))
    apply Complex.ext
    · -- Real parts: Re(F(t,-x)) = Re(conj(F(t,x))) = Re(F(t,x))
      rw [starRingEnd_apply, star_def, Complex.conj_re]
      -- Work directly with h2.1:
      -- (F t (0-0) + I * F t (x-0) + (star I * 1 * F t (0-x) + star I * I * F t (x-x))).im = 0
      have key := h2.1
      simp only [sub_zero, sub_self, mul_one] at key
      rw [show (star I : ℂ) = -I from conj_I] at key
      -- Now: (F t 0 + I * F t x + (-I * F t (-x) + -I * I * F t 0)).im = 0
      have hII : -I * I = (1 : ℂ) := by rw [neg_mul, I_mul_I, neg_neg]
      rw [hII, one_mul] at key
      -- (F t 0 + I * F t x + (-I * F t (-x) + F t 0)).im = 0
      -- Im(F t 0) + Im(I * F t x) + Im(-I * F t (-x)) + Im(F t 0) = 0
      -- 0 + (F t x).re + (-(F t (-x)).re) + 0 = 0
      -- So (F t x).re = (F t (-x)).re
      have h_im_I_mul : ∀ z : ℂ, (I * z).im = z.re := by
        intro z; simp [Complex.mul_im, I_re, I_im]
      have h_im_negI_mul : ∀ z : ℂ, (-I * z).im = -z.re := by
        intro z; simp [Complex.mul_im, I_re, I_im, neg_im]
      rw [show (0 : Fin d → ℝ) - x = -x from zero_sub x] at key
      rw [Complex.add_im, Complex.add_im, Complex.add_im,
        h_im_I_mul, h_im_negI_mul] at key
      linarith [h0_im]
    · -- Imaginary parts: Im(F(t,-x)) = Im(conj(F(t,x))) = -Im(F(t,x))
      rw [starRingEnd_apply, star_def, Complex.conj_im]
      -- From h1.1: (F t (0-0) + F t (x-0) + (F t (0-x) + F t (x-x))).im = 0
      have key := h1.1
      simp only [sub_zero, sub_self] at key
      rw [show (0 : Fin d → ℝ) - x = -x from zero_sub x] at key
      -- (F t 0 + F t x + (F t (-x) + F t 0)).im = 0
      rw [Complex.add_im, Complex.add_im, Complex.add_im] at key
      linarith [h0_im]
  nonneg := by
    intro m xs c
    -- IsSemigroupGroupPD sums F(t, as_j - as_i); IsPositiveDefinite sums F(t, xs_i - xs_j).
    -- Fix: use as = -xs, so as_j - as_i = (-xs_j) - (-xs_i) = xs_i - xs_j.
    have h := hpd m c (fun _ => t / 2) (fun i => -xs i) (by intro i; linarith)
    simp only [add_halves, neg_sub_neg] at h
    exact h.2

/-- Spatial Bochner measures exist with the Fourier property.

For each t ≥ 0, there is a finite measure ν_t on ℝ^d such that
F(t, a) = ∫ e^{i⟨a,q⟩} dν_t(q).

Uses `bochner_theorem` + normalization by F(t,0).
When F(t, 0) = 0, F(t, ·) ≡ 0 by Cauchy-Schwarz for PD. -/
lemma spatial_bochner_measures {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∀ t, 0 ≤ t → ∃ (ν : Measure (Fin d → ℝ)), IsFiniteMeasure ν ∧
      ∀ a, F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂ν := by
  intro t ht
  -- Step 1: The spatial slice is PD
  have hpd_slice := spatial_slice_pd hpd t ht
  have hcont_slice := spatial_slice_continuous hcont t ht
  -- Step 2: Case split on F(t, 0)
  by_cases h0 : F t 0 = 0
  · -- Case F(t,0) = 0: by bounded_by_zero, F(t,·) ≡ 0. Take ν = 0.
    refine ⟨0, inferInstance, fun a => ?_⟩
    have : ‖F t a‖ ≤ (F t 0).re := hpd_slice.bounded_by_zero a
    rw [h0] at this; simp at this
    simp [this, integral_zero_measure]
  · -- Case F(t,0) ≠ 0: normalize φ(a) = F(t,a)/F(t,0), then apply bochner_theorem.
    -- F(t,0) is real and positive (from PD: re ≥ 0, im = 0, and ≠ 0)
    have h0_re_pos : 0 < (F t 0).re := by
      have hre := hpd_slice.eval_zero_nonneg
      have him := hpd_slice.eval_zero_real
      by_contra h_not_pos
      push_neg at h_not_pos
      have hre0 : (F t 0).re = 0 := le_antisymm h_not_pos hre
      exfalso; apply h0
      apply Complex.ext <;> simp [him, hre0]
    have h0_ne : (F t 0) ≠ 0 := h0
    -- F(t,0) is real: F(t,0) = ↑(F(t,0).re)
    have h0_eq : F t 0 = ↑(F t 0).re := by
      apply Complex.ext
      · simp
      · exact hpd_slice.eval_zero_real
    -- F(t,0).re ≠ 0
    have h0_re_ne : (F t 0).re ≠ 0 := ne_of_gt h0_re_pos
    -- Define normalized PD function on EuclideanSpace
    let toE : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
    let fromE : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ) := WithLp.equiv 2 _
    let φ : EuclideanSpace ℝ (Fin d) → ℂ := fun a => F t (fromE a) / F t 0
    -- φ is continuous
    have hφ_cont : Continuous φ := by
      exact (hcont_slice.comp (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin d => ℝ)).continuous).div_const _
    -- φ is PD
    have hφ_pd : IsPositiveDefinite φ := by
      have hpd_fromE : IsPositiveDefinite (fun a : Fin d → ℝ => F t a) := hpd_slice
      -- PD is preserved by composition with linear maps and by scalar multiplication
      -- φ = (1/F(t,0)) * (F t ∘ fromE), and fromE is a linear equiv (in fact, id)
      constructor
      · intro x
        change F t (fromE (-x)) / F t 0 = starRingEnd ℂ (F t (fromE x) / F t 0)
        rw [map_div₀]
        congr 1
        · change F t (fromE (-x)) = (starRingEnd ℂ) (F t (fromE x))
          rw [show fromE (-x) = -fromE x from rfl]
          exact hpd_fromE.hermitian (fromE x)
        · rw [show (starRingEnd ℂ) (F t 0) = F t 0 from by
            rw [starRingEnd_apply, star_def]
            rw [h0_eq]; simp [Complex.conj_ofReal]]
      · intro m xs c
        -- φ(xᵢ-xⱼ) = F(t, fromE(xᵢ-xⱼ))/F(t,0) = F(t, fromE xᵢ - fromE xⱼ)/F(t,0)
        -- The PD sum is (1/F(t,0)) · ∑ c̄ᵢ cⱼ F(t, fromE xᵢ - fromE xⱼ)
        -- PD of F(t,·) gives nonneg re; dividing by F(t,0).re > 0 preserves sign
        -- Use IsPositiveDefinite.nonneg for the F t function
        have h_pd_base := hpd_fromE.nonneg m (fun i => fromE (xs i)) c
        -- The sum with φ = sum with F / F(t,0)
        -- show: (∑ c̄ᵢ cⱼ φ(xᵢ-xⱼ)).re = (∑ c̄ᵢ cⱼ F(t,...)).re / |F(t,0)|²  * F(t,0).re
        -- Since F(t,0) is real positive: simpler
        -- ∑ c̄ᵢ cⱼ (F(t,...)/F(t,0)) = (∑ c̄ᵢ cⱼ F(t,...)) / F(t,0)
        -- Rewrite with explicit unfolding of φ
        -- φ(xs i - xs j) = F t (fromE(xs i) - fromE(xs j)) / F t 0
        -- φ(xs i - xs j) = F(t, fromE(xs i - xs j)) / F(t, 0)
        -- = F(t, fromE(xs i) - fromE(xs j)) / F(t, 0)
        -- Pull (F t 0)⁻¹ out of the double sum
        have hφ_unfold : ∀ i j : Fin m,
            (starRingEnd ℂ) (c i) * c j * (φ (xs i - xs j)) =
            (starRingEnd ℂ) (c i) * c j *
              F t (fromE (xs i) - fromE (xs j)) * (F t 0)⁻¹ := by
          intro i j
          change _ * (F t _ / F t 0) = _
          rw [show fromE (xs i - xs j) = fromE (xs i) - fromE (xs j) from rfl]
          rw [div_eq_mul_inv]; ring
        simp_rw [hφ_unfold]
        simp_rw [← Finset.sum_mul]
        -- Goal: (∑ᵢ (∑ⱼ c̄ᵢ cⱼ F(t,...)) * (F t 0)⁻¹).re ≥ 0
        rw [h0_eq]
        rw [show (↑(F t 0).re : ℂ)⁻¹ = (↑((F t 0).re⁻¹) : ℂ) from by push_cast; ring]
        -- (z * ↑r).re = z.re * r
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg h_pd_base (le_of_lt (inv_pos.mpr h0_re_pos))
    -- φ(0) = 1
    have hφ_zero : φ 0 = 1 := div_self h0
    -- Apply bochner_theorem to get probability measure on EuclideanSpace
    obtain ⟨μ_prob, hμ⟩ := bochner_theorem φ hφ_cont hφ_pd hφ_zero
    obtain ⟨hμ_eq, _⟩ := hμ
    -- hμ_eq : ∀ ξ, charFun (↑μ_prob) ξ = φ ξ
    -- i.e., ∫ exp(⟪q, ξ⟫ * I) dμ_prob(q) = F(t, fromE ξ) / F(t, 0)
    -- Transfer measure to Fin d → ℝ and scale by F(t,0).re
    -- ν := F(t,0).re • μ_prob.map(fromE)
    let μ_base : Measure (Fin d → ℝ) :=
      (↑μ_prob : Measure (EuclideanSpace ℝ (Fin d))).map fromE
    let ν_val : Measure (Fin d → ℝ) :=
      ENNReal.ofReal (F t 0).re • μ_base
    -- ν_val is a finite measure (probability measure mapped and scaled)
    haveI : IsFiniteMeasure (↑μ_prob : Measure (EuclideanSpace ℝ (Fin d))) := inferInstance
    have hν_fin : IsFiniteMeasure ν_val := by
      constructor
      change ENNReal.ofReal (F t 0).re • μ_base Set.univ < ⊤
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      exact (measure_lt_top _ _)
    refine ⟨ν_val, hν_fin, fun a => ?_⟩
    -- Need: F t a = ∫ q, exp (I * ↑(∑ i, q i * a i)) ∂ν_val
    -- Step 1: F t a = F(t,0) * φ(toE a)
    have step1 : F t a = F t 0 * φ (toE a) := by
      change F t a = F t 0 * (F t (fromE (toE a)) / F t 0)
      rw [show fromE (toE a) = a from rfl]
      rw [mul_div_cancel₀ _ h0_ne]
    -- Step 2: φ(toE a) = charFun μ_prob (toE a)
    have step2 : φ (toE a) = charFun (↑μ_prob : Measure _) (toE a) := (hμ_eq (toE a)).symm
    -- Step 3: charFun uses inner product on EuclideanSpace
    -- charFun μ ξ = ∫ x, exp (⟪x, ξ⟫ * I) ∂μ
    -- For EuclideanSpace ℝ (Fin d): ⟪x, ξ⟫ = ∑ i, x i * ξ i (PiLp.inner_apply)
    -- and (toE a) i = a i, (fromE x) i = x i
    --
    -- So charFun μ_prob (toE a) = ∫_E exp((∑ i, x i * a i) * I) dμ_prob(x)
    -- The change of variables x = toE q, q = fromE x gives:
    -- = ∫_{Fin d → ℝ} exp((∑ i, q i * a i) * I) dμ_base(q)
    -- And (∑ q_i a_i) * I = I * (∑ q_i a_i) by commutativity.
    --
    -- Then F t a = F(t,0) * ∫ exp(I * ↑(∑ q_i a_i)) dμ_base
    --            = ∫ exp(I * ↑(∑ q_i a_i)) d(F(t,0).re • μ_base)
    -- since F(t,0) = ↑(F(t,0).re) and ∫ f d(c • μ) = c * ∫ f dμ.
    --
    -- Combine steps
    rw [step1, step2, charFun_apply]
    -- Goal: F t 0 * ∫ x : E, exp (⟪x, toE a⟫ * I) ∂↑μ_prob =
    --       ∫ q, exp (I * ↑(∑ i, q i * a i)) ∂ν_val
    -- The remaining proof connects charFun's inner product representation
    -- to our exponential sum representation and transfers the measure.
    --
    -- Key facts:
    -- (a) PiLp.inner_apply: ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ = ∑ i, x i * y i (for real ℝ)
    -- (b) fromE/toE are the identity function (WithLp.equiv is id)
    -- (c) integral_map + integral_smul_measure for the measure transfer
    -- (d) mul_comm for ↑r * I = I * ↑r
    --
    -- Remaining: type-level plumbing connecting charFun (inner product on
    -- EuclideanSpace) to our exp(I * ∑ q_i a_i) formulation.
    calc
      F t 0 * ∫ x : EuclideanSpace ℝ (Fin d), exp (↑(inner ℝ x (toE a)) * I) ∂↑μ_prob
          = ((F t 0).re : ℂ) *
              ∫ x : EuclideanSpace ℝ (Fin d), exp (I * ↑(∑ i : Fin d, (fromE x) i * a i)) ∂↑μ_prob := by
            rw [h0_eq]
            congr 1
            apply integral_congr_ae
            filter_upwards with x
            have hsum :
                ∑ i : Fin d, ((inner ℝ (x i) (a i) : ℝ) : ℂ) =
                  ∑ i : Fin d, ((a i : ℂ) * (x i : ℂ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hreal : inner ℝ (x i) (a i) = a i * x i := by
                exact RCLike.inner_apply (x i) (a i)
              simpa using congrArg (fun r : ℝ => (r : ℂ)) hreal
            have hexp :
                (∑ i : Fin d, ((inner ℝ (x i) (a i) : ℝ) : ℂ)) * I =
                  I * ∑ i : Fin d, ((x i : ℂ) * (a i : ℂ)) := by
              rw [hsum]
              simp [mul_comm]
            simpa [toE, fromE, PiLp.inner_apply] using congrArg Complex.exp hexp
      _ = ((F t 0).re : ℂ) *
            ∫ q : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μ_base := by
            congr 1
            symm
            simpa [μ_base, fromE] using
              (integral_map_equiv
                ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
                (μ := (↑μ_prob : Measure (EuclideanSpace ℝ (Fin d))))
                (f := fun q : Fin d → ℝ => exp (I * ↑(∑ i : Fin d, q i * a i))))
      _ = ∫ q : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂ν_val := by
            symm
            rw [show ν_val = ENNReal.ofReal (F t 0).re • μ_base from rfl, integral_smul_measure,
              ENNReal.toReal_ofReal (le_of_lt h0_re_pos)]
            change ((F t 0).re : ℂ) *
                ∫ x : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, x i * a i)) ∂μ_base =
              ((F t 0).re : ℂ) *
                ∫ q : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μ_base
            rfl

/-! ## Step 2: Temporal decomposition via BCR d=0

For each Borel B ⊆ ℝ^d, show t ↦ ν_t(B) is semigroup-PD on [0,∞),
then apply `semigroup_pd_laplace` to get Laplace measures.

Note: we use `IsSemigroupPD` (not `IsCompletelyMonotone`!) to avoid
the smoothness-at-zero issue. `semigroup_pd_laplace` handles this
via the mollifier + Prokhorov extraction. -/

/-- Auxiliary: for any nonneg measurable function `g` with
`g(q) = |∑ₖ dₖ e^{i⟨aₖ,q⟩}|²`, the function `t ↦ ∫ g dν_t`
is semigroup-PD.

The proof uses the "n × m product index" trick: apply `hpd`
with n·m test points, where the coefficients factor as cᵢ · dₖ
and the times/spatial vectors are (tᵢ, aₖ). The resulting double
sum factors into `∑ᵢⱼ c̄ᵢ cⱼ · ∫ |∑ₖ dₖ e^{i⟨aₖ,q⟩}|² dν_{tᵢ+tⱼ}`,
and the PD condition gives nonnegativity. -/
private lemma trig_poly_integral_pd {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (hts : ∀ i, 0 ≤ ts i)
    (m : ℕ) (dd : Fin m → ℂ) (as : Fin m → (Fin d → ℝ)) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        ↑(∫ q : Fin d → ℝ,
            (Complex.normSq (∑ k : Fin m, dd k *
              exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
          ∂(ν (ts i + ts j)))).re := by
  sorry

/-- Approximation of indicator functions by nonneg trigonometric
polynomial integrals.

For any finite measure `μ` on `ℝ^d` and measurable `B`,
the integrals `∫ |∑ dₖ e^{i⟨aₖ,q⟩}|² dμ` can approximate `μ(B)`
(from above and below, via Fejér kernel convolution on compact
exhaustions + dominated convergence). This, combined with the PD
property of `trig_poly_integral_pd`, transfers PD to `t ↦ ν_t(B)`.

Standard result in Fourier analysis; the formalization requires:
- Stone-Weierstrass on compact subsets of ℝ^d (trig polys separate points)
- Dominated convergence on compact exhaustions K_n ↑ ℝ^d
- Inner regularity of finite Borel measures on ℝ^d -/
private lemma indicator_approx_by_trig_polys {d : ℕ}
    (ν : Measure (Fin d → ℝ)) [IsFiniteMeasure ν]
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (dd : Fin m → ℂ) (as : Fin m → (Fin d → ℝ)),
      |∫ q : Fin d → ℝ,
          (Complex.normSq (∑ k : Fin m, dd k *
            exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
        ∂ν - (ν B).toReal| < ε := by
  sorry

/-- For each Borel B, the function t ↦ ν_t(B) is semigroup-PD.

Uses the "n × m product index" trick: any nonneg trigonometric
polynomial `g = |∑ dₖ e^{i⟨aₖ,·⟩}|²` has semigroup-PD integrals
(`trig_poly_integral_pd`), and such functions approximate `1_B`
in L¹(ν_t) (`indicator_approx_by_trig_polys`), so the PD
condition passes to the limit. -/
theorem spatial_measures_pd {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    IsSemigroupPD (fun t => ((ν t) B).toReal) := by
  intro n c ts hts
  -- Goal: 0 ≤ Re(∑ᵢⱼ c̄ᵢ cⱼ (ν(tᵢ+tⱼ))(B).toReal)
  -- Strategy: approximate (ν_t B).toReal by ∫ |trig poly|² dν_t,
  -- use trig_poly_integral_pd, and pass to the limit.
  --
  -- The PD sum S = ∑ᵢⱼ c̄ᵢ cⱼ r_{ij} where r_{ij} ∈ ℝ.
  -- For each ε > 0 and each (i,j), approximate r_{ij} = ν_{tᵢ+tⱼ}(B)
  -- by ∫ |trig poly|² dν_{tᵢ+tⱼ} to within ε.
  -- The PD sum with trig poly integrals is ≥ 0 by trig_poly_integral_pd.
  -- Sending ε → 0, the limit (= original sum) is ≥ 0.
  by_contra h_neg
  push_neg at h_neg
  -- S < 0. Pick ε small enough that the approximation stays negative.
  set S := (∑ i : Fin n, ∑ j : Fin n,
    star (c i) * c j * (((ν (ts i + ts j)) B).toReal : ℂ)).re with hS_def
  -- We have S < 0
  -- Bound: |S - S_approx| ≤ ∑ᵢⱼ |c̄ᵢ cⱼ| · ε
  -- So for ε < |S| / (∑ᵢⱼ |c̄ᵢ cⱼ|), S_approx < 0.
  -- But S_approx ≥ 0 by trig_poly_integral_pd. Contradiction.
  set M := ∑ i : Fin n, ∑ j : Fin n, Complex.abs (star (c i) * c j)
  -- Pick ε = |S| / (M + 1) > 0
  have hS_neg : S < 0 := h_neg
  set ε := (-S) / (M + 1) with hε_def
  have hε_pos : 0 < ε := by
    apply div_pos (neg_pos.mpr hS_neg)
    positivity
  -- For each time tᵢ + tⱼ, get approximating trig poly
  -- (We need a single trig poly that works for all relevant measures
  -- ν_{tᵢ+tⱼ}. Use the max approximation error.)
  -- Actually, we just need: for each (i,j), ∃ trig poly with
  -- |∫ |poly|² dν_{tᵢ+tⱼ} - ν_{tᵢ+tⱼ}(B)| < ε.
  -- Then the total error in S is ≤ M · ε < |S|, contradiction.
  -- For simplicity, use a SINGLE trig poly for ALL (i,j) pairs.
  -- (This is possible by taking a common refinement / max of all
  -- approximation requirements.)
  --
  -- Actually, it's easier to use a SEPARATE approximation for each
  -- (i,j) pair and bound the total error.
  sorry

/-! ## Step 3: Product measure assembly

Given spatial measures ν_t and their temporal Laplace decomposition
(from `semigroup_pd_laplace` applied to each t ↦ ν_t(B)),
construct a single measure μ on [0,∞) × ℝ^d reproducing the
Fourier-Laplace transform. -/

/-- Product measure assembly: combine the spatial Bochner measures
and their temporal Laplace decompositions into a single product
measure μ on [0,∞) × ℝ^d.

## Proof sketch (converting from axiom to sorry)

**Goal:** From the spatial Bochner measures `ν_t` and the semigroup-PD
property of `t ↦ ν_t(B)`, construct a single measure `μ` on
`[0,∞) × ℝ^d` such that `F(t,a) = ∫ e^{-tp} e^{i⟨a,q⟩} dμ(p,q)`.

### Step A: Temporal Laplace decomposition of ν_t(B)

For each Borel `B ⊆ ℝ^d`, `t ↦ (ν_t B).toReal` is semigroup-PD by
`hνPD`. To apply `semigroup_pd_laplace`, we additionally need:

1. **Continuity** of `t ↦ (ν_t B).toReal` on `[0,∞)`:
   This follows from the continuity of `F` (via `hcont`) and the
   Fourier uniqueness theorem: `ν_t` is the unique measure with
   Fourier transform `a ↦ F(t,a)`, so continuity of `F` in `t`
   implies weak continuity of `t ↦ ν_t`, hence continuity of
   `t ↦ ν_t(B)` for continuity sets `B`. Extension to all Borel
   sets uses regularity of finite measures.

2. **Boundedness** of `t ↦ (ν_t B).toReal`:
   Since `(ν_t B).toReal ≤ (ν_t univ).toReal` and
   `ν_t(univ) = (F t 0).re` (Fourier at `a=0`) and `‖F t 0‖ ≤ C`,
   we get the uniform bound `(ν_t B).toReal ≤ C`.

Given these, `semigroup_pd_laplace` yields for each Borel `B`:
a finite measure `σ_B` on `ℝ` with `σ_B(Iio 0) = 0` and
`(ν_t B).toReal = ∫ e^{-tp} dσ_B(p)` for `t ≥ 0`.

### Step B: The family B ↦ σ_B is a measure kernel

The map `B ↦ σ_B` defines a transition kernel from `ℝ` to
`Fin d → ℝ` (for each `p ∈ ℝ`, we need a measure on `Fin d → ℝ`).

More precisely, for fixed `A ⊆ ℝ` Borel, the map `B ↦ σ_B(A)` is
countably additive (follows from: Laplace transforms of disjoint
union = sum of Laplace transforms, by uniqueness of Laplace
transforms). This gives a product set function
`μ(A × B) := σ_B(A)` on measurable rectangles, which extends to
a measure by Carathéodory.

### Step C: Fourier-Laplace verification

By construction and Fubini:
```
∫∫ e^{-tp} e^{i⟨a,q⟩} dμ(p,q) = ∫_q ∫_p e^{-tp} dσ_{dq}(p) · e^{i⟨a,q⟩}
                                  = ∫_q (ν_t)(dq) · e^{i⟨a,q⟩}
                                  = F(t,a)
```

### Dependencies not yet in Mathlib

- Weak continuity of measures from Fourier transform continuity
- Carathéodory extension from consistent product set functions
- Fubini for transition kernels

These are standard results in measure theory but require substantial
formalization infrastructure not yet available. -/
theorem product_measure_assembly {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (hνPD : ∀ B, MeasurableSet B →
      IsSemigroupPD (fun t => ((ν t) B).toReal)) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ ((Set.Iio 0).prod Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          exp (-(↑(t * p.1) : ℂ)) *
            exp (I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ := by
  -- Step A: For each Borel B, apply semigroup_pd_laplace to t ↦ ν_t(B).
  -- Requires continuity and boundedness (see proof sketch above).
  -- Step B: Assemble B ↦ σ_B into a product measure via Carathéodory.
  -- Step C: Verify the Fourier-Laplace representation via Fubini.
  sorry

/-! ## Main theorem -/

/-- **BCR Theorem 4.1.13** — semigroup Bochner (general d).

Bounded continuous semigroup-PD functions on `[0,∞) × ℝ^d` are
Fourier-Laplace transforms of finite positive measures supported on
`[0,∞) × ℝ^d`.

Assembles: spatial Bochner (Step 1) + temporal PD (Step 2) +
product measure (Step 3, using `semigroup_pd_laplace` from BCR_d0). -/
theorem semigroupGroupBochner_proof (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ ((Set.Iio 0).prod Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          exp (-(↑(t * p.1) : ℂ)) *
            exp (I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ := by
  -- Step 1: Spatial Bochner measures
  have hν_exists := spatial_bochner_measures F hcont hbdd hpd
  -- Choose a consistent family (via axiom of choice)
  choose ν hν_fin hνF using fun t ht => hν_exists t ht
  -- For the assembly, we need a family defined for all t (extending by 0 for t < 0)
  let ν' : ℝ → Measure (Fin d → ℝ) := fun t =>
    if h : 0 ≤ t then ν t h else 0
  have hν'_fin : ∀ t, 0 ≤ t → IsFiniteMeasure (ν' t) := by
    intro t ht; simp only [ν', dif_pos ht]; exact hν_fin t ht
  have hν'F : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν' t) := by
    intro t ht a; simp only [ν', dif_pos ht]; exact hνF t ht a
  -- Step 2: Each t ↦ ν'_t(B) is semigroup-PD
  have hν'PD : ∀ B, MeasurableSet B →
      IsSemigroupPD (fun t => ((ν' t) B).toReal) :=
    spatial_measures_pd F hpd ν' hν'_fin hν'F
  -- Step 3: Product measure assembly
  exact product_measure_assembly F hcont hbdd hpd ν' hν'_fin hν'F hν'PD

end
