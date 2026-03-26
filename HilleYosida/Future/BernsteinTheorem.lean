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

import HilleYosida.SemigroupGroupDefs
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

/-- Auxiliary: for any nonneg trig polynomial `g(q) = |∑ₖ dₖ e^{i⟨aₖ,q⟩}|²`,
the function `t ↦ ∫ g dν_t` is semigroup-PD.

**Proof**: Apply `IsSemigroupGroupPD` with `n · m` test points indexed
by `(i, k) ∈ Fin n × Fin m`, where:
- coefficients: `c'_{(i,k)} = cᵢ · dₖ`
- times: `ts'_{(i,k)} = tsᵢ`
- spatial vectors: `as'_{(i,k)} = asₖ`

The PD sum equals `∑ᵢⱼ c̄ᵢ cⱼ · (∑ₖₗ d̄ₖ dₗ F(tᵢ+tⱼ, aₗ-aₖ))`.
Substituting the Fourier representation and computing:
`∑ₖₗ d̄ₖ dₗ F(t, aₗ-aₖ) = ∫ |∑ₖ dₖ e^{i⟨aₖ,q⟩}|² dν_t(q)`,
giving the desired inequality. -/
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
  -- Step 1: Apply IsSemigroupGroupPD with n·m product test points
  let e := finProdFinEquiv (m := n) (n := m)
  let c' : Fin (n * m) → ℂ := fun p => c (e.symm p).1 * dd (e.symm p).2
  let ts' : Fin (n * m) → ℝ := fun p => ts (e.symm p).1
  let as' : Fin (n * m) → (Fin d → ℝ) := fun p => as (e.symm p).2
  have hts' : ∀ p, 0 ≤ ts' p := fun p => hts _
  have hPD := (hpd (n * m) c' ts' as' hts').2
  -- Helper: ‖exp(I * ↑r)‖ = 1
  have norm_exp_I : ∀ r : ℝ, ‖exp (I * ↑r)‖ = 1 := fun r => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I r
  -- Step 2: Key inner equality (complex-valued):
  -- ↑(∫ normSq(...) dν_t) = ∑_k ∑_l star(dd k) * dd l * F(t, as l - as k)
  have inner_eq : ∀ (t : ℝ) (ht : 0 ≤ t),
      (↑(∫ q : Fin d → ℝ,
          (Complex.normSq (∑ k : Fin m, dd k *
            exp (I * ↑(∑ r : Fin d, q r * (as k) r))) : ℝ)
        ∂(ν t)) : ℂ) =
      ∑ k : Fin m, ∑ l : Fin m,
        star (dd k) * dd l * F t (as l - as k) := by
    intro t ht
    haveI : IsFiniteMeasure (ν t) := hν t ht
    simp_rw [hνF t ht]
    have hint : ∀ k l, Integrable (fun q : Fin d → ℝ =>
        star (dd k) * dd l *
          exp (I * ↑(∑ r : Fin d, q r * (as l - as k) r))) (ν t) := by
      intro k l
      apply Integrable.const_mul
      apply (integrable_const (1 : ℂ)).mono
      · exact Continuous.aestronglyMeasurable (by fun_prop)
      · exact ae_of_all _ (fun q => by
          rw [norm_one]; exact le_of_eq (norm_exp_I _))
    -- Pull sums outside integrals
    have pull_sums : ∑ k : Fin m, ∑ l : Fin m,
        star (dd k) * dd l *
          ∫ q, exp (I * ↑(∑ r : Fin d, q r * (as l - as k) r)) ∂(ν t) =
      ∫ q, ∑ k : Fin m, ∑ l : Fin m,
        star (dd k) * dd l *
          exp (I * ↑(∑ r : Fin d, q r * (as l - as k) r)) ∂(ν t) := by
      symm
      rw [integral_finset_sum _ (fun k _ =>
        integrable_finset_sum _ (fun l _ => hint k l))]
      apply Finset.sum_congr rfl; intro k _
      rw [integral_finset_sum _ (fun l _ => hint k l)]
      apply Finset.sum_congr rfl; intro l _
      exact integral_const_mul _ _
    rw [pull_sums]
    -- Pointwise normSq expansion
    have pointwise : ∀ q : Fin d → ℝ,
        ∑ k : Fin m, ∑ l : Fin m,
          star (dd k) * dd l *
            exp (I * ↑(∑ r : Fin d, q r * (as l - as k) r)) =
        ↑(Complex.normSq (∑ k : Fin m, dd k *
            exp (I * ↑(∑ r : Fin d, q r * (as k) r)))) := by
      intro q
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [map_sum, map_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      have hce : ∀ (s : ℝ), (starRingEnd ℂ) (cexp (I * ↑s)) =
          cexp (-(I * ↑s)) := by
        intro s
        rw [← Complex.exp_conj, map_mul, Complex.conj_I,
            Complex.conj_ofReal, neg_mul]
      have hcomb :
          (starRingEnd ℂ) (cexp (I * ↑(∑ r : Fin d, q r * (as k) r))) *
            cexp (I * ↑(∑ r : Fin d, q r * (as l) r)) =
          cexp (I * ↑(∑ r : Fin d, q r * (as l - as k) r)) := by
        rw [hce, ← Complex.exp_add]
        congr 1; push_cast
        simp only [Pi.sub_apply, Complex.ofReal_sub]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        ring
      simp only [star_def]
      rw [show (starRingEnd ℂ) (dd k) *
            (starRingEnd ℂ) (cexp (I * ↑(∑ r : Fin d, q r * (as k) r))) *
            (dd l * cexp (I * ↑(∑ r : Fin d, q r * (as l) r))) =
          (starRingEnd ℂ) (dd k) * dd l *
            ((starRingEnd ℂ) (cexp (I * ↑(∑ r : Fin d, q r * (as k) r))) *
              cexp (I * ↑(∑ r : Fin d, q r * (as l) r)))
        from by ring]
      rw [hcomb]
    conv_rhs =>
      arg 2; ext q; rw [pointwise q]
    exact (integral_ofReal).symm
  -- Step 3: Assemble: target.re = PD_sum.re ≥ 0
  suffices h_eq_re :
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          ↑(∫ q : Fin d → ℝ,
              (Complex.normSq (∑ k : Fin m, dd k *
                exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
            ∂(ν (ts i + ts j)))).re =
      (∑ p : Fin (n * m), ∑ q : Fin (n * m),
        star (c' p) * c' q *
          F (ts' p + ts' q) (as' q - as' p)).re by
    rw [h_eq_re]; exact hPD
  -- Substitute inner_eq into each summand
  have h_lhs : ∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        ↑(∫ q : Fin d → ℝ,
            (Complex.normSq (∑ k : Fin m, dd k *
              exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
          ∂(ν (ts i + ts j))) =
    ∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        (∑ k : Fin m, ∑ l : Fin m,
          star (dd k) * dd l * F (ts i + ts j) (as l - as k)) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [inner_eq _ (add_nonneg (hts i) (hts j))]
  -- Factor as quadruple sum and swap k,j indices
  have h_factor : ∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        (∑ k : Fin m, ∑ l : Fin m,
          star (dd k) * dd l * F (ts i + ts j) (as l - as k)) =
    ∑ i : Fin n, ∑ k : Fin m, ∑ j : Fin n, ∑ l : Fin m,
      star (c i) * star (dd k) * (c j * dd l) *
        F (ts i + ts j) (as l - as k) := by
    apply Finset.sum_congr rfl; intro i _
    rw [show ∑ j : Fin n,
          star (c i) * c j *
            (∑ k : Fin m, ∑ l : Fin m,
              star (dd k) * dd l * F (ts i + ts j) (as l - as k)) =
        ∑ j : Fin n, ∑ k : Fin m, ∑ l : Fin m,
          star (c i) * star (dd k) * (c j * dd l) *
            F (ts i + ts j) (as l - as k) from by
      apply Finset.sum_congr rfl; intro j _
      simp_rw [Finset.mul_sum]; ring]
    rw [Finset.sum_comm]
  -- Reindex quadruple sum to PD sum via finProdFinEquiv
  have h_reindex : ∑ i : Fin n, ∑ k : Fin m,
      ∑ j : Fin n, ∑ l : Fin m,
        star (c i) * star (dd k) * (c j * dd l) *
          F (ts i + ts j) (as l - as k) =
    ∑ p : Fin (n * m), ∑ q : Fin (n * m),
      star (c' p) * c' q *
        F (ts' p + ts' q) (as' q - as' p) := by
    rw [← Fintype.sum_prod_type']
    rw [← e.sum_comp]
    congr 1; ext p
    rw [← Fintype.sum_prod_type']
    rw [← e.sum_comp]
    congr 1; ext q
    simp only [c', ts', as', star_mul, e.symm_apply_apply]
    ring
  rw [h_lhs, h_factor, h_reindex]

/-- **Axiom: Simultaneous trig polynomial approximation of indicators.**

For finitely many finite measures on ℝ^d, indicator functions 1_B can be
simultaneously approximated in L¹ by nonneg trig polynomials |∑ d_k e^{i⟨a_k,·⟩}|².

**Proof route** (not formalized):
1. Inner regularity: approximate B by compact K with μ_i(B \ K) < ε/3 for all i
   (using the average measure μ_avg = (1/N)∑ μ_i for uniformity)
2. Urysohn: find continuous f with 1_K ≤ f ≤ 1_B
3. Stone-Weierstrass on the one-point compactification: approximate f by
   nonneg trig polynomials |∑ d_k e^{i⟨a_k,·⟩}|² uniformly on a large compact set
   (trig polys separate points in ℝ^d and are closed under conjugation)
4. Dominated convergence: ∫ |poly - 1_B| dμ_i < ε

**Mathlib dependencies**: Inner regularity of finite Borel measures on ℝ^d
(`MeasureTheory.InnerRegular`), Stone-Weierstrass for locally compact spaces. -/
axiom indicator_approx_simultaneous {d : ℕ}
    {N : ℕ} (μs : Fin N → Measure (Fin d → ℝ))
    (hfin : ∀ i, IsFiniteMeasure (μs i))
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (dd : Fin m → ℂ) (as : Fin m → (Fin d → ℝ)),
      ∀ i : Fin N,
        |∫ q : Fin d → ℝ,
            (Complex.normSq (∑ k : Fin m, dd k *
              exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
          ∂(μs i) - ((μs i) B).toReal| < ε

/-- For each Borel B, the function t ↦ ν_t(B) is semigroup-PD.

**Proof structure:**

1. Suppose for contradiction that the PD sum `S < 0` for some
   `n, c, ts`.
2. Let `M = ∑ᵢⱼ ‖c̄ᵢ cⱼ‖` and pick `ε = (-S) / (2(M + 1)) > 0`.
3. By `indicator_approx_simultaneous`, find a single trig polynomial
   `g = |∑ dₖ e^{i⟨aₖ,·⟩}|²` such that for ALL pairs `(i,j)`:
   `|∫ g dν_{tᵢ+tⱼ} - ν_{tᵢ+tⱼ}(B)| < ε`.
4. The approximation error in the PD sum satisfies
   `|S - S_approx| ≤ M · ε < |S| / 2`, so `S_approx < 0`.
5. But `S_approx ≥ 0` by `trig_poly_integral_pd`. Contradiction. -/
theorem spatial_measures_pd {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    IsSemigroupPD (fun t => ((ν t) B).toReal) := by
  intro n c ts hts
  -- Goal: 0 ≤ Re(∑ᵢⱼ c̄ᵢ cⱼ (ν(tᵢ+tⱼ)(B)).toReal)
  -- Notation: for trig poly (m, dd, as_poly), define:
  --   r(s) := ∫ |∑ dₖ e^{i⟨aₖ,q⟩}|² dν_s  (trig poly integral)
  --   v(s) := (ν s B).toReal                 (measure of B)
  -- We show ∑ c̄ᵢ cⱼ v(tᵢ+tⱼ) ≥ 0 by approximating v by r.
  by_contra h_neg
  push_neg at h_neg
  -- The PD sum is negative
  -- Coefficient bound
  set M := ∑ i : Fin n, ∑ j : Fin n, ‖star (c i) * c j‖
  have hM_nonneg : 0 ≤ M := Finset.sum_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))
  -- Pick ε small enough
  set S := (∑ i : Fin n, ∑ j : Fin n,
    star (c i) * c j *
      (((ν (ts i + ts j)) B).toReal : ℂ)).re
  have hS_neg : S < 0 := h_neg
  set ε := (-S) / (2 * (M + 1))
  have hε_pos : 0 < ε := by
    apply div_pos (neg_pos.mpr hS_neg); positivity
  -- Define the n² measures indexed by Fin (n * n)
  let idx := finProdFinEquiv (m := n) (n := n)
  let μs : Fin (n * n) → Measure (Fin d → ℝ) :=
    fun p => ν (ts (idx.symm p).1 + ts (idx.symm p).2)
  have hμs_fin : ∀ p, IsFiniteMeasure (μs p) := by
    intro p; exact hν _ (add_nonneg (hts _) (hts _))
  -- Get a single trig poly approximating 1_B for all n² measures
  obtain ⟨m, dd, as_poly, h_approx⟩ :=
    indicator_approx_simultaneous μs hμs_fin B hB ε hε_pos
  -- For each (i,j), the trig poly integral approximates ν_{tᵢ+tⱼ}(B)
  -- Let r(s) = ∫ |poly|² dν_s
  let r : ℝ → ℝ := fun s => ∫ q : Fin d → ℝ,
    (Complex.normSq (∑ k : Fin m, dd k *
      exp (I * ↑(∑ l : Fin d, q l * (as_poly k) l))) : ℝ) ∂(ν s)
  have h_approx_ij : ∀ i j : Fin n,
      |r (ts i + ts j) - ((ν (ts i + ts j)) B).toReal| < ε := by
    intro i j
    have h := h_approx (idx (i, j))
    simp only [μs, Equiv.symm_apply_apply] at h
    exact h
  -- The trig poly PD sum is nonneg: ∑ c̄ᵢ cⱼ r(tᵢ+tⱼ) ≥ 0
  have h_pd := trig_poly_integral_pd F hpd ν hν hνF
    n c ts hts m dd as_poly
  -- h_pd : 0 ≤ (∑ i j, c̄ᵢ cⱼ ↑(r(tᵢ+tⱼ))).re
  -- Now bound |∑ c̄ᵢ cⱼ (r(tᵢ+tⱼ) - v(tᵢ+tⱼ))| ≤ M · ε
  -- which gives S ≥ S' - M·ε ≥ -M·ε > S (contradiction)
  -- where S' = Re(∑ c̄ᵢ cⱼ r(tᵢ+tⱼ)) ≥ 0.
  --
  -- Error bound: M * ε < -S
  have h_bound : M * ε < -S := by
    -- ε = (-S) / (2(M+1)), so M·ε = M·(-S)/(2(M+1)) < -S
    -- because M < 2(M+1).
    rw [show ε = (-S) / (2 * (M + 1)) from rfl]
    have hS_pos : 0 < -S := neg_pos.mpr hS_neg
    calc M * ((-S) / (2 * (M + 1)))
        = M * (-S) / (2 * (M + 1)) := by ring
      _ ≤ (M + 1) * (-S) / (2 * (M + 1)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith) hS_pos.le
      _ = (-S) / 2 := by field_simp
      _ < -S := by linarith
  -- Bound the norm of the difference sum
  -- |Re(∑ c̄ᵢcⱼ(↑r(tᵢ+tⱼ) - ↑v(tᵢ+tⱼ)))| ≤ M · ε
  have h_err : |((∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j * ((r (ts i + ts j) : ℂ) -
        (((ν (ts i + ts j)) B).toReal : ℂ))).re)| ≤ M * ε := by
    calc _ ≤ ‖∑ i : Fin n, ∑ j : Fin n,
            star (c i) * c j * ((r (ts i + ts j) : ℂ) -
              (((ν (ts i + ts j)) B).toReal : ℂ))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ∑ i, ‖∑ j, star (c i) * c j *
            ((r (ts i + ts j) : ℂ) -
              (((ν (ts i + ts j)) B).toReal : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖star (c i) * c j *
            ((r (ts i + ts j) : ℂ) -
              (((ν (ts i + ts j)) B).toReal : ℂ))‖ :=
          Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ = ∑ i, ∑ j, ‖star (c i) * c j‖ *
            ‖(r (ts i + ts j) : ℂ) -
              (((ν (ts i + ts j)) B).toReal : ℂ)‖ := by
          congr 1; ext i; congr 1; ext j; exact norm_mul _ _
      _ ≤ ∑ i, ∑ j, ‖star (c i) * c j‖ * ε := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [show (r (ts i + ts j) : ℂ) -
            (((ν (ts i + ts j)) B).toReal : ℂ) =
            ((r (ts i + ts j) -
              ((ν (ts i + ts j)) B).toReal : ℝ) : ℂ) from by
              push_cast; ring]
          rw [Complex.norm_real]
          exact le_of_lt (h_approx_ij i j)
      _ = M * ε := by
          rw [show (∑ i : Fin n, ∑ j : Fin n,
            ‖star (c i) * c j‖ * ε) =
            (∑ i : Fin n, ∑ j : Fin n,
              ‖star (c i) * c j‖) * ε from by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro i _
            exact (Finset.sum_mul _ _ _).symm]
  -- The difference of the sums:
  -- (∑ c̄ᵢcⱼ ↑r(tᵢ+tⱼ)).re - S
  -- = Re(∑ c̄ᵢcⱼ(↑r(tᵢ+tⱼ) - ↑v(tᵢ+tⱼ)))
  have h_split : (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j * (r (ts i + ts j) : ℂ)).re - S =
    (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j * ((r (ts i + ts j) : ℂ) -
        (((ν (ts i + ts j)) B).toReal : ℂ))).re := by
    -- ∑ cᵢⱼ(rᵢⱼ - vᵢⱼ) = ∑ cᵢⱼ rᵢⱼ - ∑ cᵢⱼ vᵢⱼ, then take Re
    have h_expand : (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j * ((r (ts i + ts j) : ℂ) -
          (((ν (ts i + ts j)) B).toReal : ℂ))) =
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j * (r (ts i + ts j) : ℂ)) -
      (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          (((ν (ts i + ts j)) B).toReal : ℂ)) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [h_expand, Complex.sub_re]
  -- Combine: 0 ≤ S' and S = S' - err with |err| ≤ M·ε < -S
  -- So S ≥ S' - M·ε ≥ 0 - M·ε > S. Contradiction.
  have hS' := h_pd  -- 0 ≤ (∑ c̄ᵢcⱼ ↑r(tᵢ+tⱼ)).re
  -- From h_split: S = (∑ c̄ᵢcⱼ ↑r).re - err where |err| ≤ M·ε
  -- So S ≥ (∑ c̄ᵢcⱼ ↑r).re - M·ε ≥ -M·ε
  -- But M·ε < -S, so S > S. Contradiction.
  linarith [abs_le.mp h_err, h_split]

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
formalization infrastructure not yet available.

**Axiom: Product measure assembly from temporal Laplace decomposition.**

Given spatial Bochner measures ν_t with semigroup-PD mass functions,
construct a single product measure μ on [0,∞) × ℝ^d reproducing the
Fourier-Laplace transform.

**Proof route** (not formalized):
1. For each Borel B, apply `semigroup_pd_laplace` to `t ↦ ν_t(B).toReal`
   (requires: continuity from Fourier uniqueness, boundedness from ν_t(B) ≤ F(t,0) ≤ C)
   to get σ_B on [0,∞) with `ν_t(B) = ∫ e^{-tp} dσ_B(p)`
2. The family B ↦ σ_B is a measure kernel: for fixed Borel A ⊆ [0,∞),
   B ↦ σ_B(A) is countably additive (from countable additivity of ν_t
   + uniqueness of Laplace transforms)
3. Define μ via Carathéodory: μ(A × B) = σ_B(A) on measurable rectangles
4. Verify F(t,a) = ∫∫ e^{-tp} e^{i⟨a,q⟩} dμ(p,q) via Fubini

**Mathlib dependencies**: Transition kernel construction from consistent
set functions, Fubini-Tonelli for transition kernels, uniqueness of
Laplace transform on [0,∞). -/
axiom product_measure_assembly {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
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
          ∂μ

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
