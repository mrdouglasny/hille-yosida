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
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Weierstrass

noncomputable section

open MeasureTheory Complex Set Filter Finset
open scoped Polynomial

private noncomputable def expNegToUnitInterval (p : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-max p 0), by
    constructor
    · positivity
    · have hmax : 0 ≤ max p 0 := le_max_right _ _
      have h : Real.exp (-max p 0) ≤ 1 := by
        exact Real.exp_le_one_iff.mpr (by linarith)
      exact h⟩

private lemma continuous_expNegToUnitInterval : Continuous expNegToUnitInterval := by
  have h : Continuous fun p : ℝ => Real.exp (-max p 0) := by
    fun_prop
  simpa [expNegToUnitInterval] using
    h.subtype_mk (fun p => by
      constructor
      · positivity
      · have hmax : 0 ≤ max p 0 := le_max_right _ _
        have h' : Real.exp (-max p 0) ≤ 1 := by
          exact Real.exp_le_one_iff.mpr (by linarith)
        simpa using h')

private lemma measurable_expNegToUnitInterval : Measurable expNegToUnitInterval :=
  continuous_expNegToUnitInterval.measurable

private lemma coe_expNegToUnitInterval_of_nonneg {p : ℝ} (hp : 0 ≤ p) :
    (expNegToUnitInterval p : ℝ) = Real.exp (-p) := by
  simp [expNegToUnitInterval, hp]

private lemma coe_expNegToUnitInterval_of_neg {p : ℝ} (hp : p < 0) :
    (expNegToUnitInterval p : ℝ) = 1 := by
  simp [expNegToUnitInterval, max_eq_right (le_of_lt hp), Real.exp_zero]

private noncomputable def laplacePushforwardUnit (μ : Measure ℝ) :
    Measure (Set.Icc (0 : ℝ) 1) :=
  μ.map expNegToUnitInterval

private lemma laplacePushforwardUnit_moment_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hsupp : μ (Set.Iio 0) = 0) (n : ℕ) :
    ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂(laplacePushforwardUnit μ) =
      ∫ p : ℝ, Real.exp (-((n : ℝ) * p)) ∂μ := by
  rw [laplacePushforwardUnit, integral_map measurable_expNegToUnitInterval.aemeasurable]
  · apply integral_congr_ae
    refine ae_iff.mpr ?_
    refine measure_mono_null (fun p hp => ?_) hsupp
    by_cases hneg : p < 0
    · exact hneg
    · have hnonneg : 0 ≤ p := le_of_not_gt hneg
      exfalso
      apply hp
      change (expNegToUnitInterval p : ℝ) ^ n = Real.exp (-((n : ℝ) * p))
      rw [coe_expNegToUnitInterval_of_nonneg hnonneg, ← Real.exp_nat_mul]
      congr 1
      ring
  · exact (continuous_subtype_val.pow n).aestronglyMeasurable

private lemma laplacePushforwardUnit_moments_eq_of_laplace_eq
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμsupp : μ (Set.Iio 0) = 0) (hνsupp : ν (Set.Iio 0) = 0)
    (h_eq : ∀ t, 0 ≤ t → ∫ p : ℝ, Real.exp (-(t * p)) ∂μ =
      ∫ p : ℝ, Real.exp (-(t * p)) ∂ν) :
    ∀ n : ℕ,
      ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂(laplacePushforwardUnit μ) =
        ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂(laplacePushforwardUnit ν) := by
  intro n
  rw [laplacePushforwardUnit_moment_eq μ hμsupp n,
    laplacePushforwardUnit_moment_eq ν hνsupp n]
  exact h_eq n (Nat.cast_nonneg n)

private lemma poly_integrable_unitInterval
    (μ : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure μ] (p : ℝ[X]) :
    Integrable (fun x : Set.Icc (0 : ℝ) 1 => Polynomial.eval (x : ℝ) p) μ := by
  let f : C(Set.Icc (0 : ℝ) 1, ℝ) := p.toContinuousMapOn (Set.Icc (0 : ℝ) 1)
  have hbcf : Integrable (⇑(BoundedContinuousFunction.mkOfCompact f)) μ :=
    BoundedContinuousFunction.integrable (μ := μ)
      ((ContinuousMap.equivBoundedOfCompact (Set.Icc (0 : ℝ) 1) ℝ) f)
  simpa [f, Polynomial.toContinuousMapOn] using hbcf

private lemma poly_integral_eq_of_moments_eq
    (μ ν : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℕ,
      ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂μ =
        ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂ν)
    (p : ℝ[X]) :
    ∫ x : Set.Icc (0 : ℝ) 1, Polynomial.eval (x : ℝ) p ∂μ =
      ∫ x : Set.Icc (0 : ℝ) 1, Polynomial.eval (x : ℝ) p ∂ν := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simp only [Polynomial.eval_add]
    rw [integral_add (poly_integrable_unitInterval μ p) (poly_integrable_unitInterval μ q),
      integral_add (poly_integrable_unitInterval ν p) (poly_integrable_unitInterval ν q),
      hp, hq]
  · intro n a
    simp [Polynomial.eval_monomial, hm n, integral_const_mul]

private noncomputable def expNegOnIci : Set.Ici (0 : ℝ) → Set.Icc (0 : ℝ) 1 :=
  fun p => ⟨Real.exp (-p.1), by
    constructor
    · positivity
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr p.2)⟩

private lemma measurable_expNegOnIci : Measurable expNegOnIci := by
  refine Measurable.subtype_mk ?_
  exact Real.measurable_exp.comp measurable_subtype_coe.neg

private noncomputable def logInvOnIcc : Set.Icc (0 : ℝ) 1 → Set.Ici (0 : ℝ) :=
  fun x => ⟨-Real.log (x : ℝ), neg_nonneg.mpr (Real.log_nonpos x.2.1 x.2.2)⟩

private lemma measurable_logInvOnIcc : Measurable logInvOnIcc := by
  refine Measurable.subtype_mk ?_
  exact (Real.measurable_log.comp measurable_subtype_coe).neg

private lemma range_expNegOnIci :
    Set.range expNegOnIci = {x : Set.Icc (0 : ℝ) 1 | 0 < (x : ℝ)} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact Real.exp_pos _
  · intro hx
    refine ⟨⟨-Real.log (x : ℝ), neg_nonneg.mpr (Real.log_nonpos x.2.1 x.2.2)⟩, ?_⟩
    apply Subtype.ext
    dsimp [expNegOnIci]
    change Real.exp (-(-Real.log (x : ℝ))) = (x : ℝ)
    simpa using Real.exp_log hx

private lemma measurableSet_range_expNegOnIci : MeasurableSet (Set.range expNegOnIci) := by
  rw [range_expNegOnIci]
  exact measurable_subtype_coe measurableSet_Ioi

private lemma leftInverse_logInvOnIcc : Function.LeftInverse logInvOnIcc expNegOnIci := by
  intro p
  apply Subtype.ext
  change -Real.log (Real.exp (-↑p)) = ↑p
  rw [Real.log_exp]
  ring

private lemma measurableEmbedding_expNegOnIci : MeasurableEmbedding expNegOnIci := by
  exact MeasurableEmbedding.of_measurable_inverse measurable_expNegOnIci
    measurableSet_range_expNegOnIci measurable_logInvOnIcc leftInverse_logInvOnIcc

private lemma restrict_eq_self_of_support_nonneg
    (μ : Measure ℝ) (hsupp : μ (Set.Iio 0) = 0) :
    μ.restrict (Set.Ici 0) = μ := by
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa [Set.compl_Ici] using hsupp

private lemma laplacePushforwardUnit_eq_map_onIci
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hsupp : μ (Set.Iio 0) = 0) :
    laplacePushforwardUnit μ =
      Measure.map expNegOnIci (μ.comap (fun x : Set.Ici (0 : ℝ) => (x : ℝ))) := by
  calc
    laplacePushforwardUnit μ = Measure.map expNegToUnitInterval (μ.restrict (Set.Ici 0)) := by
      simpa [laplacePushforwardUnit] using
        congrArg (Measure.map expNegToUnitInterval) (restrict_eq_self_of_support_nonneg μ hsupp).symm
    _ =
        Measure.map expNegToUnitInterval
          (Measure.map (fun x : Set.Ici (0 : ℝ) => (x : ℝ))
            (μ.comap (fun x : Set.Ici (0 : ℝ) => (x : ℝ)))) := by
          rw [← map_comap_subtype_coe measurableSet_Ici]
    _ =
        Measure.map (expNegToUnitInterval ∘ fun x : Set.Ici (0 : ℝ) => (x : ℝ))
          (μ.comap (fun x : Set.Ici (0 : ℝ) => (x : ℝ))) := by
            rw [Measure.map_map measurable_expNegToUnitInterval measurable_subtype_coe]
    _ = Measure.map expNegOnIci (μ.comap (fun x : Set.Ici (0 : ℝ) => (x : ℝ))) := by
      congr 1
      ext x
      simp [Function.comp, expNegOnIci, expNegToUnitInterval]

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

private lemma fourier_integral_continuous {d : ℕ} (μ : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ] :
    Continuous fun a : Fin d → ℝ =>
      ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μ := by
  apply MeasureTheory.continuous_of_dominated
  · intro a
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · intro a
    refine ae_of_all _ fun q => ?_
    exact le_of_eq (by simpa [mul_comm] using
      Complex.norm_exp_ofReal_mul_I (∑ i : Fin d, q i * a i))
  · simpa using (integrable_const (1 : ℝ))
  · refine ae_of_all _ ?_
    intro q
    apply Continuous.cexp
    apply Continuous.mul continuous_const
    apply continuous_ofReal.comp
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)

private lemma positive_definite_to_finite_measure {d : ℕ} (φ : (Fin d → ℝ) → ℂ)
    (hcont : Continuous φ) (hpd : IsPositiveDefinite φ) :
    ∃ (μ : Measure (Fin d → ℝ)), IsFiniteMeasure μ ∧
      ∀ a, φ a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μ := by
  by_cases h0 : φ 0 = 0
  · refine ⟨0, inferInstance, fun a => ?_⟩
    have : ‖φ a‖ ≤ (φ 0).re := hpd.bounded_by_zero a
    rw [h0] at this
    simp at this
    simp [this, integral_zero_measure]
  · have h0_re_pos : 0 < (φ 0).re := by
      have hre := hpd.eval_zero_nonneg
      have him := hpd.eval_zero_real
      by_contra h_not_pos
      push_neg at h_not_pos
      have hre0 : (φ 0).re = 0 := le_antisymm h_not_pos hre
      exfalso
      apply h0
      apply Complex.ext <;> simp [him, hre0]
    have h0_eq : φ 0 = ↑(φ 0).re := by
      apply Complex.ext
      · simp
      · exact hpd.eval_zero_real
    have h0_ne : φ 0 ≠ 0 := h0
    let toE : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
    let fromE : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ) := WithLp.equiv 2 _
    let ψ : EuclideanSpace ℝ (Fin d) → ℂ := fun a => φ (fromE a) / φ 0
    have hψ_cont : Continuous ψ := by
      exact (hcont.comp (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin d => ℝ)).continuous).div_const _
    have hψ_pd : IsPositiveDefinite ψ := by
      have hpd_fromE : IsPositiveDefinite (fun a : Fin d → ℝ => φ a) := hpd
      constructor
      · intro x
        change φ (fromE (-x)) / φ 0 = starRingEnd ℂ (φ (fromE x) / φ 0)
        rw [map_div₀]
        congr 1
        · change φ (fromE (-x)) = (starRingEnd ℂ) (φ (fromE x))
          rw [show fromE (-x) = -fromE x from rfl]
          exact hpd_fromE.hermitian (fromE x)
        · rw [show (starRingEnd ℂ) (φ 0) = φ 0 from by
            rw [starRingEnd_apply, star_def]
            rw [h0_eq]
            simp [Complex.conj_ofReal]]
      · intro m xs c
        have h_pd_base := hpd_fromE.nonneg m (fun i => fromE (xs i)) c
        have hψ_unfold : ∀ i j : Fin m,
            (starRingEnd ℂ) (c i) * c j * (ψ (xs i - xs j)) =
            (starRingEnd ℂ) (c i) * c j *
              φ (fromE (xs i) - fromE (xs j)) * (φ 0)⁻¹ := by
          intro i j
          change _ * (φ _ / φ 0) = _
          rw [show fromE (xs i - xs j) = fromE (xs i) - fromE (xs j) from rfl]
          rw [div_eq_mul_inv]
          ring
        simp_rw [hψ_unfold]
        simp_rw [← Finset.sum_mul]
        rw [h0_eq]
        rw [show (↑(φ 0).re : ℂ)⁻¹ = (↑((φ 0).re⁻¹) : ℂ) from by
          push_cast
          ring]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        exact mul_nonneg h_pd_base (le_of_lt (inv_pos.mpr h0_re_pos))
    have hψ_zero : ψ 0 = 1 := div_self h0
    obtain ⟨μ_prob, hμ⟩ := bochner_theorem ψ hψ_cont hψ_pd hψ_zero
    obtain ⟨hμ_eq, _⟩ := hμ
    let μ_base : Measure (Fin d → ℝ) :=
      (↑μ_prob : Measure (EuclideanSpace ℝ (Fin d))).map fromE
    let μ_val : Measure (Fin d → ℝ) :=
      ENNReal.ofReal (φ 0).re • μ_base
    haveI : IsFiniteMeasure (↑μ_prob : Measure (EuclideanSpace ℝ (Fin d))) := inferInstance
    have hμ_fin : IsFiniteMeasure μ_val := by
      constructor
      change ENNReal.ofReal (φ 0).re * μ_base Set.univ < ⊤
      apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      exact measure_lt_top _ _
    refine ⟨μ_val, hμ_fin, fun a => ?_⟩
    have step1 : φ a = φ 0 * ψ (toE a) := by
      change φ a = φ 0 * (φ (fromE (toE a)) / φ 0)
      rw [show fromE (toE a) = a from rfl]
      rw [mul_div_cancel₀ _ h0_ne]
    have step2 : ψ (toE a) = charFun (↑μ_prob : Measure _) (toE a) := (hμ_eq (toE a)).symm
    rw [step1, step2, charFun_apply]
    calc
      φ 0 * ∫ x : EuclideanSpace ℝ (Fin d), exp (↑(inner ℝ x (toE a)) * I) ∂↑μ_prob
          = ((φ 0).re : ℂ) *
              ∫ x : EuclideanSpace ℝ (Fin d),
                exp (I * ↑(∑ i : Fin d, (fromE x) i * a i)) ∂↑μ_prob := by
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
      _ = ((φ 0).re : ℂ) *
            ∫ q : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μ_base := by
            congr 1
            symm
            simpa [μ_base, fromE] using
              (integral_map_equiv
                ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)
                (μ := (↑μ_prob : Measure (EuclideanSpace ℝ (Fin d))))
                (f := fun q : Fin d → ℝ => exp (I * ↑(∑ i : Fin d, q i * a i))))
      _ = ∫ q : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μ_val := by
            symm
            rw [show μ_val = ENNReal.ofReal (φ 0).re • μ_base from rfl, integral_smul_measure,
              ENNReal.toReal_ofReal (le_of_lt h0_re_pos)]
            rfl

private lemma fourier_uniqueness_finite_measure {d : ℕ}
    (μ ν : Measure (Fin d → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_eq : ∀ a : Fin d → ℝ,
      ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μ =
        ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂ν) :
    μ = ν := by
  let toE : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := WithLp.toLp 2
  let fromE : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ) := WithLp.equiv 2 _
  have hmeas_toE : Measurable toE := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
  have hmeas_fromE : Measurable fromE :=
    ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurable)
  have hmap : μ.map toE = ν.map toE := by
    apply Measure.ext_of_charFun
    ext a
    rw [charFun_apply, charFun_apply]
    have hμ :
        ∫ x : EuclideanSpace ℝ (Fin d), exp (↑(inner ℝ x a) * I) ∂(μ.map toE) =
          ∫ q : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, q i * fromE a i)) ∂μ := by
      change ∫ x : EuclideanSpace ℝ (Fin d), exp (↑(inner ℝ x a) * I) ∂
          (Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) μ) = _
      rw [integral_map_equiv (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        (μ := μ) (f := fun x : EuclideanSpace ℝ (Fin d) => exp (↑(inner ℝ x a) * I))]
      apply integral_congr_ae
      filter_upwards with q
      have hsum :
          ∑ i : Fin d, ((inner ℝ (toE q i) (a i) : ℝ) : ℂ) =
            ∑ i : Fin d, (((fromE a i : ℝ) : ℂ) * (q i : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hreal : inner ℝ (toE q i) (a i) = fromE a i * q i := by
          exact RCLike.inner_apply (toE q i) (a i)
        simpa [toE, fromE] using congrArg (fun r : ℝ => (r : ℂ)) hreal
      have hexp :
          (∑ i : Fin d, ((inner ℝ (toE q i) (a i) : ℝ) : ℂ)) * I =
            I * ∑ i : Fin d, ((q i : ℂ) * ((fromE a i : ℝ) : ℂ)) := by
        rw [hsum]
        simp [mul_comm]
      simpa [PiLp.inner_apply, toE, fromE] using congrArg Complex.exp hexp
    have hν :
        ∫ x : EuclideanSpace ℝ (Fin d), exp (↑(inner ℝ x a) * I) ∂(ν.map toE) =
          ∫ q : Fin d → ℝ, exp (I * ↑(∑ i : Fin d, q i * fromE a i)) ∂ν := by
      change ∫ x : EuclideanSpace ℝ (Fin d), exp (↑(inner ℝ x a) * I) ∂
          (Measure.map (MeasurableEquiv.toLp 2 (Fin d → ℝ)) ν) = _
      rw [integral_map_equiv (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        (μ := ν) (f := fun x : EuclideanSpace ℝ (Fin d) => exp (↑(inner ℝ x a) * I))]
      apply integral_congr_ae
      filter_upwards with q
      have hsum :
          ∑ i : Fin d, ((inner ℝ (toE q i) (a i) : ℝ) : ℂ) =
            ∑ i : Fin d, (((fromE a i : ℝ) : ℂ) * (q i : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hreal : inner ℝ (toE q i) (a i) = fromE a i * q i := by
          exact RCLike.inner_apply (toE q i) (a i)
        simpa [toE, fromE] using congrArg (fun r : ℝ => (r : ℂ)) hreal
      have hexp :
          (∑ i : Fin d, ((inner ℝ (toE q i) (a i) : ℝ) : ℂ)) * I =
            I * ∑ i : Fin d, ((q i : ℂ) * ((fromE a i : ℝ) : ℂ)) := by
        rw [hsum]
        simp [mul_comm]
      simpa [PiLp.inner_apply, toE, fromE] using congrArg Complex.exp hexp
    rw [hμ, hν, h_eq (fromE a)]
  have hback := congrArg (fun ρ : Measure (EuclideanSpace ℝ (Fin d)) => ρ.map fromE) hmap
  change Measure.map fromE (Measure.map toE μ) = Measure.map fromE (Measure.map toE ν) at hback
  rw [Measure.map_map hmeas_fromE hmeas_toE,
    Measure.map_map hmeas_fromE hmeas_toE] at hback
  have hcomp : fromE ∘ toE = id := by
    ext q i
    rfl
  simpa [hcomp] using hback

private lemma fourier_kernel_integrable {d : ℕ} (μ : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ] (a : Fin d → ℝ) :
    Integrable (fun q : Fin d → ℝ => exp (I * ↑(∑ i : Fin d, q i * a i))) μ := by
  apply (integrable_const (1 : ℂ)).mono
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine ae_of_all _ fun q => ?_
    exact le_of_eq (by simpa [mul_comm] using
      (Complex.norm_exp_ofReal_mul_I (∑ i : Fin d, q i * a i)))

private lemma weighted_sum_positive_definite {d n : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (x : Fin n → ℝ) (ts : Fin n → ℝ) (hts : ∀ i, 0 ≤ ts i) :
    IsPositiveDefinite (fun a : Fin d → ℝ =>
      ∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) a) := by
  refine ⟨?_, ?_⟩
  · intro a
    calc
      ∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) (-a)
          = ∑ r : Fin n, ∑ s : Fin n,
              starRingEnd ℂ (((x r * x s : ℝ) : ℂ) * F (ts r + ts s) a) := by
              apply Finset.sum_congr rfl
              intro r _
              apply Finset.sum_congr rfl
              intro s _
              have hs :=
                (spatial_slice_pd hpd (ts r + ts s) (add_nonneg (hts r) (hts s))).hermitian a
              simp [hs, Complex.conj_ofReal, mul_assoc, mul_left_comm, mul_comm]
      _ = starRingEnd ℂ
            (∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) a) := by
              simp_rw [map_sum]
  · intro m as c
    let e := finProdFinEquiv (m := m) (n := n)
    let c' : Fin (m * n) → ℂ := fun p => c (e.symm p).1 * (x (e.symm p).2 : ℂ)
    let ts' : Fin (m * n) → ℝ := fun p => ts (e.symm p).2
    let as' : Fin (m * n) → (Fin d → ℝ) := fun p => -as (e.symm p).1
    have hts' : ∀ p, 0 ≤ ts' p := fun p => hts _
    have hPD := (hpd (m * n) c' ts' as' hts').2
    have h_factor :
        ∑ i : Fin m, ∑ j : Fin m,
          star (c i) * c j *
            (∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) (as i - as j)) =
        ∑ i : Fin m, ∑ r : Fin n, ∑ j : Fin m, ∑ s : Fin n,
          star (c i) * (x r : ℂ) * (c j * (x s : ℂ)) *
            F (ts r + ts s) (as i - as j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show ∑ j : Fin m,
            star (c i) * c j *
              (∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) (as i - as j)) =
          ∑ j : Fin m, ∑ r : Fin n, ∑ s : Fin n,
            star (c i) * (x r : ℂ) * (c j * (x s : ℂ)) *
              F (ts r + ts s) (as i - as j) from by
        apply Finset.sum_congr rfl
        intro j _
        simp_rw [Finset.mul_sum]
        simp_rw [Complex.ofReal_mul]
        ring]
      rw [Finset.sum_comm]
    have h_reindex :
        ∑ i : Fin m, ∑ r : Fin n, ∑ j : Fin m, ∑ s : Fin n,
          star (c i) * (x r : ℂ) * (c j * (x s : ℂ)) *
            F (ts r + ts s) (as i - as j) =
        ∑ p : Fin (m * n), ∑ q : Fin (m * n),
          star (c' p) * c' q * F (ts' p + ts' q) (as' q - as' p) := by
      rw [← Fintype.sum_prod_type']
      rw [← e.sum_comp]
      congr 1
      ext p
      rw [← Fintype.sum_prod_type']
      rw [← e.sum_comp]
      congr 1
      ext q
      simp only [c', ts', as', star_mul, e.symm_apply_apply]
      have hp : star (x p.2 : ℂ) = (x p.2 : ℂ) := by simp
      rw [hp]
      ring
    have h_complex :
        ∑ i : Fin m, ∑ j : Fin m,
          star (c i) * c j *
            (∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) (as i - as j)) =
        ∑ p : Fin (m * n), ∑ q : Fin (m * n),
          star (c' p) * c' q * F (ts' p + ts' q) (as' q - as' p) := by
      rw [h_factor, h_reindex]
    have : 0 ≤
        (∑ i : Fin m, ∑ j : Fin m,
          star (c i) * c j *
            (∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) (as i - as j))).re := by
      rw [h_complex]
      exact hPD
    simpa using this

private lemma real_max_sub_max_neg (z : ℝ) : max z 0 - max (-z) 0 = z := by
  by_cases hz : 0 ≤ z
  · have hneg : -z ≤ 0 := by linarith
    simp [max_eq_left hz, max_eq_right hneg]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    have hneg : 0 ≤ -z := by linarith
    simp [max_eq_right hz', max_eq_left hneg]

private lemma weighted_measure_fourier {d n : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (w : Fin n → Fin n → ℝ) (hw : ∀ r s, 0 ≤ w r s)
    (ts : Fin n → ℝ) (hts : ∀ i, 0 ≤ ts i) (a : Fin d → ℝ) :
    ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂
      (∑ r : Fin n, ∑ s : Fin n, ENNReal.ofReal (w r s) • ν (ts r + ts s)) =
      ∑ r : Fin n, ∑ s : Fin n, ((w r s : ℝ) : ℂ) * F (ts r + ts s) a := by
  let f : (Fin d → ℝ) → ℂ := fun q => exp (I * ↑(∑ i : Fin d, q i * a i))
  let μrow : Fin n → Measure (Fin d → ℝ) := fun r =>
    ∑ s : Fin n, ENNReal.ofReal (w r s) • ν (ts r + ts s)
  have h_term_int :
      ∀ r s : Fin n, Integrable f (ENNReal.ofReal (w r s) • ν (ts r + ts s)) := by
    intro r s
    haveI : IsFiniteMeasure (ν (ts r + ts s)) := hν _ (add_nonneg (hts r) (hts s))
    exact (fourier_kernel_integrable (μ := ν (ts r + ts s)) a).smul_measure
      ENNReal.ofReal_ne_top
  have h_row_int : ∀ r : Fin n, Integrable f (μrow r) := by
    intro r
    simpa [μrow] using (MeasureTheory.integrable_finset_sum_measure
      (f := f)
      (μ := fun s : Fin n => ENNReal.ofReal (w r s) • ν (ts r + ts s))
      (s := Finset.univ)).2 (fun s hs => h_term_int r s)
  change ∫ q, f q ∂(∑ r : Fin n, μrow r) =
      ∑ r : Fin n, ∑ s : Fin n, ((w r s : ℝ) : ℂ) * F (ts r + ts s) a
  rw [integral_finset_sum_measure
    (f := f)
    (μ := μrow)
    (s := Finset.univ)
    (fun r hr => h_row_int r)]
  apply Finset.sum_congr rfl
  intro r hr
  change ∫ q, f q ∂(∑ s : Fin n, ENNReal.ofReal (w r s) • ν (ts r + ts s)) =
      ∑ s : Fin n, ((w r s : ℝ) : ℂ) * F (ts r + ts s) a
  rw [integral_finset_sum_measure
    (f := f)
    (μ := fun s : Fin n => ENNReal.ofReal (w r s) • ν (ts r + ts s))
    (s := Finset.univ)
    (fun s hs => h_term_int r s)]
  apply Finset.sum_congr rfl
  intro s hs
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hw r s), hνF _ (add_nonneg (hts r) (hts s)) a]
  change ((w r s : ℝ) : ℂ) * ∫ (q : Fin d → ℝ),
      exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν (ts r + ts s)) =
    ((w r s : ℝ) : ℂ) * ∫ (q : Fin d → ℝ),
      exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν (ts r + ts s))
  rfl

private lemma weighted_measure_eval {d n : ℕ}
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (w : Fin n → Fin n → ℝ) (hw : ∀ r s, 0 ≤ w r s)
    (ts : Fin n → ℝ) (hts : ∀ i, 0 ≤ ts i)
    (B : Set (Fin d → ℝ)) :
    ((∑ r : Fin n, ∑ s : Fin n, ENNReal.ofReal (w r s) • ν (ts r + ts s)) B).toReal =
      ∑ r : Fin n, ∑ s : Fin n, w r s * ((ν (ts r + ts s)) B).toReal := by
  let term : Fin n → Fin n → ENNReal := fun r s =>
    ENNReal.ofReal (w r s) * ν (ts r + ts s) B
  let row : Fin n → ENNReal := fun r => ∑ s : Fin n, term r s
  have h_term_top : ∀ r s : Fin n, term r s ≠ ⊤ := by
    intro r s
    haveI : IsFiniteMeasure (ν (ts r + ts s)) := hν _ (add_nonneg (hts r) (hts s))
    dsimp [term]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top (ν (ts r + ts s)) B)
  have h_row_top : ∀ r : Fin n, row r ≠ ⊤ := by
    intro r
    dsimp [row]
    exact (ENNReal.sum_ne_top).2 (fun s _ => h_term_top r s)
  rw [show ((∑ r : Fin n, ∑ s : Fin n, ENNReal.ofReal (w r s) • ν (ts r + ts s)) B).toReal =
      (∑ r : Fin n, ∑ s : Fin n, term r s).toReal by
      simp [term, Measure.smul_apply, mul_comm, mul_left_comm, mul_assoc]]
  rw [show (∑ r : Fin n, ∑ s : Fin n, term r s).toReal =
      ∑ r : Fin n, (row r).toReal by
      simpa [row] using (ENNReal.toReal_sum (s := (Finset.univ : Finset (Fin n)))
        (fun r hr => h_row_top r))]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show (row r).toReal =
      ∑ s : Fin n, (term r s).toReal by
      simpa [row] using (ENNReal.toReal_sum (s := (Finset.univ : Finset (Fin n)))
        (fun s hs => h_term_top r s))]
  apply Finset.sum_congr rfl
  intro s hs
  simp [term, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw r s), mul_assoc, mul_left_comm, mul_comm]

private lemma spatial_measures_pd_real {d n : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (B : Set (Fin d → ℝ))
    (x : Fin n → ℝ) (ts : Fin n → ℝ) (hts : ∀ i, 0 ≤ ts i) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * x j * ((ν (ts i + ts j)) B).toReal := by
  let G : (Fin d → ℝ) → ℂ := fun a =>
    ∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) a
  have hG_cont : Continuous G := by
    unfold G
    apply continuous_finset_sum _ fun r _ =>
      continuous_finset_sum _ fun s _ => by
        haveI : IsFiniteMeasure (ν (ts r + ts s)) := hν _ (add_nonneg (hts r) (hts s))
        have hfun : (fun a : Fin d → ℝ => F (ts r + ts s) a) =
            fun a : Fin d → ℝ =>
              ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν (ts r + ts s)) := by
          funext a
          exact hνF _ (add_nonneg (hts r) (hts s)) a
        simpa [hfun] using
          (continuous_const.mul (fourier_integral_continuous (μ := ν (ts r + ts s))))
  have hG_pd : IsPositiveDefinite G := weighted_sum_positive_definite F hpd x ts hts
  obtain ⟨η, hηfin, hηG⟩ := positive_definite_to_finite_measure G hG_cont hG_pd
  haveI : IsFiniteMeasure η := hηfin
  let wplus : Fin n → Fin n → ℝ := fun r s => max (x r * x s) 0
  let wminus : Fin n → Fin n → ℝ := fun r s => max (-(x r * x s)) 0
  let μPlus : Measure (Fin d → ℝ) :=
    ∑ r : Fin n, ∑ s : Fin n, ENNReal.ofReal (wplus r s) • ν (ts r + ts s)
  let μMinus : Measure (Fin d → ℝ) :=
    ∑ r : Fin n, ∑ s : Fin n, ENNReal.ofReal (wminus r s) • ν (ts r + ts s)
  have hwplus : ∀ r s, 0 ≤ wplus r s := by
    intro r s
    simp [wplus]
  have hwminus : ∀ r s, 0 ≤ wminus r s := by
    intro r s
    simp [wminus]
  haveI hplus_term (r s : Fin n) :
      IsFiniteMeasure (ENNReal.ofReal (wplus r s) • ν (ts r + ts s)) := by
    haveI : IsFiniteMeasure (ν (ts r + ts s)) := hν _ (add_nonneg (hts r) (hts s))
    constructor
    change ENNReal.ofReal (wplus r s) * ν (ts r + ts s) Set.univ < ⊤
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  haveI hminus_term (r s : Fin n) :
      IsFiniteMeasure (ENNReal.ofReal (wminus r s) • ν (ts r + ts s)) := by
    haveI : IsFiniteMeasure (ν (ts r + ts s)) := hν _ (add_nonneg (hts r) (hts s))
    constructor
    change ENNReal.ofReal (wminus r s) * ν (ts r + ts s) Set.univ < ⊤
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  haveI : IsFiniteMeasure μPlus := by
    unfold μPlus
    infer_instance
  haveI : IsFiniteMeasure μMinus := by
    unfold μMinus
    infer_instance
  have h_fourier_eq :
      ∀ a : Fin d → ℝ,
        ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂μPlus =
          ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(μMinus + η) := by
    intro a
    rw [integral_add_measure (fourier_kernel_integrable (μ := μMinus) a)
      (fourier_kernel_integrable (μ := η) a)]
    rw [weighted_measure_fourier F ν hν hνF wplus hwplus ts hts a]
    rw [weighted_measure_fourier F ν hν hνF wminus hwminus ts hts a]
    rw [← hηG a]
    have hGa : G a = ∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) a := rfl
    rw [hGa]
    calc
      ∑ r : Fin n, ∑ s : Fin n, ((wplus r s : ℝ) : ℂ) * F (ts r + ts s) a
          = ∑ r : Fin n, ∑ s : Fin n,
              ((((wminus r s : ℝ) : ℂ) + ((x r * x s : ℝ) : ℂ)) * F (ts r + ts s) a) := by
                apply Finset.sum_congr rfl
                intro r hr
                apply Finset.sum_congr rfl
                intro s hs
                have hsplit :
                    (wplus r s : ℝ) = wminus r s + x r * x s := by
                  dsimp [wplus, wminus]
                  linarith [real_max_sub_max_neg (x r * x s)]
                rw [show ((wplus r s : ℝ) : ℂ) =
                    ((wminus r s : ℝ) : ℂ) + ((x r * x s : ℝ) : ℂ) from by
                  calc
                    ((wplus r s : ℝ) : ℂ) = ↑(wminus r s + x r * x s) := by
                      exact congrArg (fun z : ℝ => (z : ℂ)) hsplit
                    _ = ((wminus r s : ℝ) : ℂ) + ((x r * x s : ℝ) : ℂ) := by
                      simp]
      _ = ∑ r : Fin n, ∑ s : Fin n,
            (((wminus r s : ℝ) : ℂ) * F (ts r + ts s) a +
              ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) a) := by
                apply Finset.sum_congr rfl
                intro r hr
                apply Finset.sum_congr rfl
                intro s hs
                ring
      _ = (∑ r : Fin n, ∑ s : Fin n, ((wminus r s : ℝ) : ℂ) * F (ts r + ts s) a) +
            ∑ r : Fin n, ∑ s : Fin n, ((x r * x s : ℝ) : ℂ) * F (ts r + ts s) a := by
                simpa [add_mul, Finset.sum_add_distrib]
      _ = (∑ r : Fin n, ∑ s : Fin n, ((wminus r s : ℝ) : ℂ) * F (ts r + ts s) a) + G a := by
                rfl
  have hμ_eq : μPlus = μMinus + η :=
    fourier_uniqueness_finite_measure μPlus (μMinus + η) h_fourier_eq
  have h_eval :
      (μPlus B).toReal = (μMinus B).toReal + (η B).toReal := by
    have h_apply : μPlus B = (μMinus + η) B := congrArg (fun ρ : Measure (Fin d → ℝ) => ρ B) hμ_eq
    have h_toReal := congrArg ENNReal.toReal (by simpa [Measure.add_apply] using h_apply)
    simpa [ENNReal.toReal_add] using h_toReal
  have h_plus_eval :
      (μPlus B).toReal =
        ∑ r : Fin n, ∑ s : Fin n, wplus r s * ((ν (ts r + ts s)) B).toReal :=
    weighted_measure_eval ν hν wplus hwplus ts hts B
  have h_minus_eval :
      (μMinus B).toReal =
        ∑ r : Fin n, ∑ s : Fin n, wminus r s * ((ν (ts r + ts s)) B).toReal :=
    weighted_measure_eval ν hν wminus hwminus ts hts B
  have hsplit_sum :
      (∑ i : Fin n, ∑ j : Fin n, x i * x j * ((ν (ts i + ts j)) B).toReal) =
        (∑ i : Fin n, ∑ j : Fin n, wplus i j * ((ν (ts i + ts j)) B).toReal) -
        (∑ i : Fin n, ∑ j : Fin n, wminus i j * ((ν (ts i + ts j)) B).toReal) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, x i * x j * ((ν (ts i + ts j)) B).toReal)
          = ∑ i : Fin n, ∑ j : Fin n,
              (wplus i j - wminus i j) * ((ν (ts i + ts j)) B).toReal := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                have hij :
                    x i * x j = wplus i j - wminus i j := by
                  dsimp [wplus, wminus]
                  exact (real_max_sub_max_neg (x i * x j)).symm
                rw [hij]
      _ = ∑ i : Fin n, ∑ j : Fin n,
            (wplus i j * ((ν (ts i + ts j)) B).toReal -
              wminus i j * ((ν (ts i + ts j)) B).toReal) := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                ring
      _ = (∑ i : Fin n, ∑ j : Fin n, wplus i j * ((ν (ts i + ts j)) B).toReal) -
            (∑ i : Fin n, ∑ j : Fin n, wminus i j * ((ν (ts i + ts j)) B).toReal) := by
                simp_rw [Finset.sum_sub_distrib]
  have hmain :
      (∑ i : Fin n, ∑ j : Fin n, x i * x j * ((ν (ts i + ts j)) B).toReal) = (η B).toReal := by
    rw [hsplit_sum, ← h_plus_eval, ← h_minus_eval]
    linarith
  rw [hmain]
  exact ENNReal.toReal_nonneg

/-- For each Borel B, the function t ↦ ν_t(B) is semigroup-PD.

The proof uses the finite-measure Fourier uniqueness route:
for real coefficients, split the weighted family into positive and negative
finite measures, build the positive-definite Fourier transform via Bochner,
identify measures by uniqueness of Fourier transforms, then reduce the
complex-coefficient case to the real and imaginary parts. -/
theorem spatial_measures_pd {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    IsSemigroupPD (fun t => ((ν t) B).toReal) := by
  intro n c ts hts
  let M : Fin n → Fin n → ℝ := fun i j => ((ν (ts i + ts j)) B).toReal
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * ((M i j : ℝ) : ℂ)).re =
        ∑ i : Fin n, ∑ j : Fin n,
          (((c i).re * (c j).re + (c i).im * (c j).im) * M i j) := by
    simp [M, Complex.mul_re, mul_comm]
  have hsplit' :
      (∑ i : Fin n, ∑ j : Fin n,
        (((c i).re * (c j).re + (c i).im * (c j).im) * M i j)) =
        (∑ i : Fin n, ∑ j : Fin n, (c i).re * (c j).re * M i j) +
        (∑ i : Fin n, ∑ j : Fin n, (c i).im * (c j).im * M i j) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
  have hre :
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, (c i).re * (c j).re * M i j :=
    spatial_measures_pd_real F hpd ν hν hνF B (fun i => (c i).re) ts hts
  have him :
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, (c i).im * (c j).im * M i j :=
    spatial_measures_pd_real F hpd ν hν hνF B (fun i => (c i).im) ts hts
  rw [hsplit, hsplit']
  linarith

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
