/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.
-/

import HilleYosida.BCR.d0
import Bochner.Main
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.ContinuousMap.Weierstrass

/-! # BCR Theorem 4.1.13 — shared toolkit

Private analytic helpers (Laplace pushforward to the unit interval, polynomial
density on `[0,1]`, exponential measurable embedding `expNegOnIci`) feeding the
uniqueness clause, plus the shared `TemporalSliceRep` record consumed by both
the existence assembly and the uniqueness argument.

The only declarations exposed across files are `TemporalSliceRep`,
`temporalSliceRepOf`, `TemporalSliceRep.iUnion_eq`, and `laplace_measure_unique`. -/

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
          congrArg (Measure.map expNegToUnitInterval)
          (restrict_eq_self_of_support_nonneg μ hsupp).symm
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

private lemma unitInterval_measure_unique_of_moments_eq
    (μ ν : Measure (Set.Icc (0 : ℝ) 1)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : ∀ n : ℕ,
      ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂μ =
        ∫ x : Set.Icc (0 : ℝ) 1, (x : ℝ) ^ n ∂ν) :
    μ = ν := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  let f : C(Set.Icc (0 : ℝ) 1, ℝ) := g.toContinuousMap
  apply eq_of_forall_dist_le
  intro ε hε
  let M : ℝ := μ.real Set.univ + ν.real Set.univ + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    positivity
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_continuousMap 0 1 f (ε / (2 * M)) (by positivity)
  let gp : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ :=
    (ContinuousMap.equivBoundedOfCompact (Set.Icc (0 : ℝ) 1) ℝ)
      (p.toContinuousMapOn (Set.Icc (0 : ℝ) 1))
  have hg_eq :
      (ContinuousMap.equivBoundedOfCompact (Set.Icc (0 : ℝ) 1) ℝ) f = g := by
    ext x
    rfl
  have hnorm' :
      ‖gp - g‖ < ε / (2 * M) := by
    rw [← hg_eq]
    simpa [gp, f] using hp
  have hnorm :
      ‖g - gp‖ < ε / (2 * M) := by
    simpa [norm_sub_rev] using hnorm'
  have hpoly :
      ∫ x, gp x ∂μ = ∫ x, gp x ∂ν := by
    simpa [gp] using poly_integral_eq_of_moments_eq μ ν hm p
  have hμdist :
      dist (∫ x, g x ∂μ) (∫ x, gp x ∂μ) ≤ μ.real Set.univ * ‖g - gp‖ := by
    have h0 := BoundedContinuousFunction.norm_integral_le_mul_norm (μ := μ) (g - gp)
    simpa [Real.dist_eq, integral_sub (g.integrable μ) (gp.integrable μ)] using h0
  have hνdist :
      dist (∫ x, g x ∂ν) (∫ x, gp x ∂ν) ≤ ν.real Set.univ * ‖g - gp‖ := by
    have h0 := BoundedContinuousFunction.norm_integral_le_mul_norm (μ := ν) (g - gp)
    simpa [Real.dist_eq, integral_sub (g.integrable ν) (gp.integrable ν)] using h0
  have hμlt : dist (∫ x, g x ∂μ) (∫ x, gp x ∂μ) < ε / 2 := by
    have hmass : μ.real Set.univ ≤ M := by
      dsimp [M]
      have hν_nonneg : 0 ≤ ν.real Set.univ := by positivity
      linarith
    have hmul :
        M * ‖g - gp‖ < M * (ε / (2 * M)) := by
      exact mul_lt_mul_of_pos_left hnorm hM_pos
    have hbound : μ.real Set.univ * ‖g - gp‖ ≤ M * ‖g - gp‖ := by
      exact mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
    calc
      dist (∫ x, g x ∂μ) (∫ x, gp x ∂μ) ≤ μ.real Set.univ * ‖g - gp‖ := hμdist
      _ ≤ M * ‖g - gp‖ := hbound
      _ < M * (ε / (2 * M)) := hmul
      _ = ε / 2 := by
        field_simp [hM_pos.ne']
  have hνlt : dist (∫ x, g x ∂ν) (∫ x, gp x ∂ν) < ε / 2 := by
    have hmass : ν.real Set.univ ≤ M := by
      dsimp [M]
      have hμ_nonneg : 0 ≤ μ.real Set.univ := by positivity
      linarith
    have hmul :
        M * ‖g - gp‖ < M * (ε / (2 * M)) := by
      exact mul_lt_mul_of_pos_left hnorm hM_pos
    have hbound : ν.real Set.univ * ‖g - gp‖ ≤ M * ‖g - gp‖ := by
      exact mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
    calc
      dist (∫ x, g x ∂ν) (∫ x, gp x ∂ν) ≤ ν.real Set.univ * ‖g - gp‖ := hνdist
      _ ≤ M * ‖g - gp‖ := hbound
      _ < M * (ε / (2 * M)) := hmul
      _ = ε / 2 := by
        field_simp [hM_pos.ne']
  exact le_of_lt <| calc
    dist (∫ x, g x ∂μ) (∫ x, g x ∂ν)
        ≤ dist (∫ x, g x ∂μ) (∫ x, gp x ∂μ) + dist (∫ x, gp x ∂μ) (∫ x, g x ∂ν) :=
          dist_triangle _ _ _
    _ = dist (∫ x, g x ∂μ) (∫ x, gp x ∂μ) + dist (∫ x, gp x ∂ν) (∫ x, g x ∂ν) := by
          rw [hpoly]
    _ < ε / 2 + ε / 2 := add_lt_add hμlt (by simpa [dist_comm] using hνlt)
    _ = ε := by ring

lemma laplace_measure_unique
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμsupp : μ (Set.Iio 0) = 0) (hνsupp : ν (Set.Iio 0) = 0)
    (h_eq : ∀ t, 0 ≤ t → ∫ p : ℝ, Real.exp (-(t * p)) ∂μ =
      ∫ p : ℝ, Real.exp (-(t * p)) ∂ν) :
    μ = ν := by
  haveI : IsFiniteMeasure (laplacePushforwardUnit μ) := by
    unfold laplacePushforwardUnit
    infer_instance
  haveI : IsFiniteMeasure (laplacePushforwardUnit ν) := by
    unfold laplacePushforwardUnit
    infer_instance
  have hpush :
      laplacePushforwardUnit μ = laplacePushforwardUnit ν :=
    unitInterval_measure_unique_of_moments_eq
      (laplacePushforwardUnit μ) (laplacePushforwardUnit ν)
      (laplacePushforwardUnit_moments_eq_of_laplace_eq μ ν hμsupp hνsupp h_eq)
  have hcomap :
      μ.comap (fun x : Set.Ici (0 : ℝ) => (x : ℝ)) =
        ν.comap (fun x : Set.Ici (0 : ℝ) => (x : ℝ)) := by
    apply (MeasurableEmbedding.map_injective measurableEmbedding_expNegOnIci)
    simpa [laplacePushforwardUnit_eq_map_onIci μ hμsupp,
      laplacePushforwardUnit_eq_map_onIci ν hνsupp] using hpush
  have hrestrict :
      μ.restrict (Set.Ici 0) = ν.restrict (Set.Ici 0) := by
    have hmap := congrArg (Measure.map (fun x : Set.Ici (0 : ℝ) => (x : ℝ))) hcomap
    rw [map_comap_subtype_coe measurableSet_Ici, map_comap_subtype_coe measurableSet_Ici] at hmap
    exact hmap
  calc
    μ = μ.restrict (Set.Ici 0) := (restrict_eq_self_of_support_nonneg μ hμsupp).symm
    _ = ν.restrict (Set.Ici 0) := hrestrict
    _ = ν := restrict_eq_self_of_support_nonneg ν hνsupp

private lemma laplace_kernel_integrable
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμsupp : μ (Set.Iio 0) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun p : ℝ => Real.exp (-(t * p))) μ := by
  refine MeasureTheory.Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id').neg).aestronglyMeasurable
  · have h_nonneg_ae : ∀ᵐ p ∂μ, 0 ≤ p := by
      refine ae_iff.2 ?_
      simpa [not_le] using hμsupp
    filter_upwards [h_nonneg_ae] with p hp
    have hle : Real.exp (-(t * p)) ≤ 1 := by
      apply (Real.exp_le_one_iff).2
      nlinarith [mul_nonneg ht hp]
    have hnonneg : 0 ≤ Real.exp (-(t * p)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle

structure TemporalSliceRep {d : ℕ}
    (ν : ℝ → Measure (Fin d → ℝ)) (B : Set (Fin d → ℝ)) where
  σ : Measure ℝ
  finite : IsFiniteMeasure σ
  support : σ (Set.Iio 0) = 0
  laplace : ∀ t, 0 ≤ t → ((ν t) B).toReal = ∫ p, Real.exp (-(t * p)) ∂σ

attribute [instance] TemporalSliceRep.finite

/-- Two temporal-slice representations are equal iff their underlying measures agree. -/
@[ext]
theorem TemporalSliceRep.ext {d : ℕ} {ν : ℝ → Measure (Fin d → ℝ)}
    {B : Set (Fin d → ℝ)} {r₁ r₂ : TemporalSliceRep ν B} (h : r₁.σ = r₂.σ) :
    r₁ = r₂ := by
  cases r₁; cases r₂; congr

noncomputable def temporalSliceRepOf {d : ℕ}
    (ν : ℝ → Measure (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    (hpdB : IsSemigroupPD (fun t => ((ν t) B).toReal))
    (hcontB : ContinuousOn (fun t => ((ν t) B).toReal) (Set.Ici 0))
    (hbddB : ∃ C : ℝ, ∀ t, 0 ≤ t → |((ν t) B).toReal| ≤ C) :
    TemporalSliceRep ν B := by
  classical
  let hslice := semigroup_pd_laplace (fun t => ((ν t) B).toReal) hpdB hcontB hbddB
  refine ⟨Classical.choose hslice, ?_, ?_, ?_⟩
  · exact (Classical.choose_spec hslice).1
  · exact (Classical.choose_spec hslice).2.1
  · exact (Classical.choose_spec hslice).2.2

private lemma TemporalSliceRep.measure_eq {d : ℕ}
    {ν : ℝ → Measure (Fin d → ℝ)} {B : Set (Fin d → ℝ)}
    (r₁ r₂ : TemporalSliceRep ν B) :
    r₁.σ = r₂.σ := by
  haveI := r₁.finite
  haveI := r₂.finite
  exact laplace_measure_unique r₁.σ r₂.σ r₁.support r₂.support (fun t ht => by
    rw [← r₁.laplace t ht, ← r₂.laplace t ht])

private lemma TemporalSliceRep.union_eq {d : ℕ}
    {ν : ℝ → Measure (Fin d → ℝ)}
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    {B₁ B₂ : Set (Fin d → ℝ)} (hB₂ : MeasurableSet B₂) (hdisj : Disjoint B₁ B₂)
    (r₁ : TemporalSliceRep ν B₁) (r₂ : TemporalSliceRep ν B₂)
    (r₁₂ : TemporalSliceRep ν (B₁ ∪ B₂)) :
    r₁₂.σ = r₁.σ + r₂.σ := by
  haveI := r₁.finite
  haveI := r₂.finite
  haveI : IsFiniteMeasure (r₁.σ + r₂.σ) := by infer_instance
  apply laplace_measure_unique r₁₂.σ (r₁.σ + r₂.σ) r₁₂.support
  · simp [Measure.add_apply, r₁.support, r₂.support]
  · intro t ht
    haveI := hν t ht
    rw [← r₁₂.laplace t ht, integral_add_measure
      (laplace_kernel_integrable r₁.σ r₁.support ht)
      (laplace_kernel_integrable r₂.σ r₂.support ht),
      ← r₁.laplace t ht, ← r₂.laplace t ht]
    rw [measure_union hdisj hB₂, ENNReal.toReal_add]
    all_goals simp [measure_ne_top]

private lemma TemporalSliceRep.mass_eq_zero {d : ℕ}
    {ν : ℝ → Measure (Fin d → ℝ)} {B : Set (Fin d → ℝ)}
    (hν0 : IsFiniteMeasure (ν 0)) (r : TemporalSliceRep ν B) :
    r.σ Set.univ = (ν 0) B := by
  haveI := hν0
  have h0 : ((ν 0) B).toReal = (r.σ Set.univ).toReal := by
    simpa [Measure.real] using r.laplace 0 le_rfl
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top r.σ Set.univ) (measure_ne_top (ν 0) B)).1 h0.symm

lemma TemporalSliceRep.iUnion_eq {d : ℕ}
    {ν : ℝ → Measure (Fin d → ℝ)}
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (B : ℕ → Set (Fin d → ℝ)) (hB : ∀ n, MeasurableSet (B n))
    (hdisj : Pairwise (Function.onFun Disjoint B))
    (r : ∀ n, TemporalSliceRep ν (B n))
    (rU : TemporalSliceRep ν (⋃ n, B n)) :
    rU.σ = Measure.sum (fun n => (r n).σ) := by
  haveI hν0 : IsFiniteMeasure (ν 0) := hν 0 le_rfl
  have hsum_univ :
      (Measure.sum (fun n => (r n).σ)) Set.univ = (ν 0) (⋃ n, B n) := by
    rw [Measure.sum_apply _ MeasurableSet.univ, measure_iUnion hdisj hB]
    simp_rw [TemporalSliceRep.mass_eq_zero hν0]
  have hsum_ne_top : (Measure.sum (fun n => (r n).σ)) Set.univ ≠ ⊤ := by
    rw [hsum_univ]
    exact measure_ne_top (ν 0) _
  haveI hsum_fin : IsFiniteMeasure (Measure.sum (fun n => (r n).σ)) := by
    constructor
    simpa [lt_top_iff_ne_top] using hsum_ne_top
  have hsum_support : (Measure.sum (fun n => (r n).σ)) (Set.Iio 0) = 0 := by
    have hzero : ∀ n, (r n).σ (Set.Iio 0) = 0 := fun n => (r n).support
    rw [Measure.sum_apply _ measurableSet_Iio]
    simp [hzero]
  apply laplace_measure_unique rU.σ (Measure.sum (fun n => (r n).σ)) rU.support hsum_support
  intro t ht
  haveI := hν t ht
  have hLap : ∀ n, ∫ p, Real.exp (-(t * p)) ∂((r n).σ) = ((ν t) (B n)).toReal := by
    intro n
    rw [← (r n).laplace t ht]
  rw [← rU.laplace t ht, integral_sum_measure
    (laplace_kernel_integrable (Measure.sum (fun n => (r n).σ)) hsum_support ht)]
  simp_rw [hLap]
  rw [measure_iUnion hdisj hB,
    ENNReal.tsum_toReal_eq (fun n => measure_ne_top (ν t) (B n))]


lemma fourier_uniqueness_finite_measure {d : ℕ}
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

end
