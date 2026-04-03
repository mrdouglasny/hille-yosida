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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
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

private lemma laplace_measure_unique
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

private structure TemporalSliceRep {d : ℕ}
    (ν : ℝ → Measure (Fin d → ℝ)) (B : Set (Fin d → ℝ)) where
  σ : Measure ℝ
  finite : IsFiniteMeasure σ
  support : σ (Set.Iio 0) = 0
  laplace : ∀ t, 0 ≤ t → ((ν t) B).toReal = ∫ p, Real.exp (-(t * p)) ∂σ

attribute [instance] TemporalSliceRep.finite

private noncomputable def temporalSliceRepOf {d : ℕ}
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

private lemma TemporalSliceRep.iUnion_eq {d : ℕ}
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
    (_hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
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
            (∑ r : Fin n, ∑ s : Fin n,
              ((x r * x s : ℝ) : ℂ) *
                F (ts r + ts s) (as i - as j))).re := by
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
      simp [term]]
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
  simp [term, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hw r s)]

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
                simp [add_mul, Finset.sum_add_distrib]
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
    (B : Set (Fin d → ℝ)) (_hB : MeasurableSet B) :
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

private lemma spatial_measure_total_mass_eq_re_zero {d : ℕ}
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    {t : ℝ} (ht : 0 ≤ t) :
    ((ν t) Set.univ).toReal = (F t 0).re := by
  haveI := hν t ht
  have h0 := hνF t ht 0
  simp only [Pi.zero_apply, mul_zero, sum_const_zero, ofReal_zero, exp_zero,
    integral_const, Measure.real] at h0
  have h0re : (F t 0).re = ((ν t) Set.univ).toReal := by
    have h0re' : (F t 0).re = (((ν t) Set.univ).toReal • (1 : ℂ)).re := by
      exact congrArg Complex.re h0
    simpa using h0re'
  exact h0re.symm

private lemma spatial_slice_bounded {d : ℕ}
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (B : Set (Fin d → ℝ)) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → |((ν t) B).toReal| ≤ C := by
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨C, ?_⟩
  intro t ht
  haveI := hν t ht
  have hmono :
      ((ν t) B).toReal ≤ ((ν t) Set.univ).toReal := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top (ν t) B)
      (measure_ne_top (ν t) Set.univ)).2 (measure_mono (Set.subset_univ B))
  calc
    |((ν t) B).toReal| = ((ν t) B).toReal := abs_of_nonneg ENNReal.toReal_nonneg
    _ ≤ ((ν t) Set.univ).toReal := hmono
    _ = (F t 0).re := spatial_measure_total_mass_eq_re_zero F ν hν hνF ht
    _ ≤ ‖F t 0‖ := Complex.re_le_norm _
    _ ≤ C := hC t 0 ht

/-! ## Step 3: Product measure assembly

Given spatial measures ν_t and their temporal Laplace decomposition
(from `semigroup_pd_laplace` applied to each t ↦ ν_t(B)),
construct a single measure μ on [0,∞) × ℝ^d reproducing the
Fourier-Laplace transform. -/

/- Product measure assembly: combine the spatial Bochner measures
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

**Remaining external inputs** after the formalized slice analysis:

1. continuity of `t ↦ ((ν t) B).toReal` from continuity of `F` and Fourier uniqueness;
2. extension of the resulting countably additive temporal slice family
   to a joint measure on `ℝ × ℝ^d`, together with the Fubini identity.

The old monolithic `product_measure_assembly` axiom is therefore reduced
to the two narrower axioms below. -/

private lemma antitone_sum_dist_le {f g S : ℝ → ℝ} {t s a : ℝ}
    (ht : a ≤ t) (hs : a ≤ s)
    (hf : AntitoneOn f (Ici a)) (hg : AntitoneOn g (Ici a))
    (hS : ∀ x ≥ a, f x + g x = S x) :
    |f t - f s| ≤ |S t - S s| := by
  by_cases h : t ≤ s
  · have hf_le : f s ≤ f t := hf ht hs h
    have hg_le : g s ≤ g t := hg ht hs h
    have hS_eq : S t - S s = (f t - f s) + (g t - g s) := by
      rw [← hS t ht, ← hS s hs]; ring
    have h1 : |f t - f s| = f t - f s := abs_of_nonneg (by linarith)
    have h2 : |S t - S s| = S t - S s := abs_of_nonneg (by linarith)
    rw [h1, h2, hS_eq]; linarith
  · push_neg at h
    have hle : s ≤ t := le_of_lt h
    have hf_le : f t ≤ f s := hf hs ht hle
    have hg_le : g t ≤ g s := hg hs ht hle
    have hS_eq : S s - S t = (f s - f t) + (g s - g t) := by
      rw [← hS s hs, ← hS t ht]; ring
    have h1 : |f t - f s| = f s - f t := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have h2 : |S t - S s| = S s - S t := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [h1, h2, hS_eq]; linarith

/-- Continuity of measurable spatial slices via the monotone squeeze trick:
t ↦ ν_t(B) and t ↦ ν_t(Bᶜ) are both decreasing (from semigroup PD),
and their sum ν_t(ℝ^d) = Re(F(t,0)) is continuous. Two decreasing functions
with continuous sum must both be continuous. -/
lemma spatial_slice_measure_continuous {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a, F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (hνPD : ∀ B, MeasurableSet B → IsSemigroupPD (fun t => ((ν t) B).toReal))
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    ContinuousOn (fun t => ((ν t) B).toReal) (Ici (0 : ℝ)) := by
  let f := fun t => ((ν t) B).toReal
  let g := fun t => ((ν t) Bᶜ).toReal
  let S := fun t => (F t 0).re
  have hbdd_f := spatial_slice_bounded F hbdd ν hν hνF B
  have hbdd_g := spatial_slice_bounded F hbdd ν hν hνF Bᶜ
  have hf_anti : AntitoneOn f (Ici 0) := by
    intro t ht s hs hts
    by_cases heq : t = s; · rw [heq]
    have h_pos : 0 < s - t := sub_pos.mpr (lt_of_le_of_ne hts heq)
    have hdiff := (hνPD B hB).alternating_forwardDiff 1 t ht (s - t) h_pos hbdd_f
    simp only [pow_one, iterForwardDiff, forwardDiff] at hdiff
    have h_add : t + (s - t) = s := by ring
    rw [h_add] at hdiff; linarith
  have hg_anti : AntitoneOn g (Ici 0) := by
    intro t ht s hs hts
    by_cases heq : t = s; · rw [heq]
    have h_pos : 0 < s - t := sub_pos.mpr (lt_of_le_of_ne hts heq)
    have hdiff := (hνPD Bᶜ hB.compl).alternating_forwardDiff 1 t ht (s - t) h_pos hbdd_g
    simp only [pow_one, iterForwardDiff, forwardDiff] at hdiff
    have h_add : t + (s - t) = s := by ring
    rw [h_add] at hdiff; linarith
  have hS_eq : ∀ x ≥ 0, f x + g x = S x := by
    intro x hx
    dsimp [f, g, S]
    haveI := hν x hx
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    rw [← measure_union (@disjoint_compl_right _ _ B) hB.compl, union_compl_self]
    exact spatial_measure_total_mass_eq_re_zero F ν hν hνF hx
  have hS_cont : ContinuousOn S (Ici 0) := by
    have : ContinuousOn (fun t => F t 0) (Ici 0) := by
      have h_emb : ContinuousOn (fun x : ℝ => (x, (0 : Fin d → ℝ))) (Ici 0) :=
        (continuous_id'.prodMk continuous_const).continuousOn
      have h_maps : MapsTo (fun x : ℝ => (x, (0 : Fin d → ℝ))) (Ici 0)
          (Ici (0 : ℝ) ×ˢ Set.univ) :=
        fun x hx => ⟨hx, Set.mem_univ _⟩
      exact hcont.comp h_emb h_maps
    exact (Complex.continuous_re.comp_continuousOn this)
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  rw [Metric.continuousOn_iff] at hS_cont
  obtain ⟨δ, hδ, hS_bound⟩ := hS_cont t ht ε hε
  refine ⟨δ, hδ, fun s hs hdist => ?_⟩
  have h_squeeze := antitone_sum_dist_le ht hs hf_anti hg_anti hS_eq
  have hS_dist : |S t - S s| < ε := by
    have := hS_bound s hs hdist
    rw [Real.dist_eq] at this
    rwa [abs_sub_comm] at this
  rw [Real.dist_eq, abs_sub_comm]
  linarith

private noncomputable def gridVec {d : ℕ} (n : ℕ) (q : Fin d → ℝ) : Fin d → ℤ :=
  fun i => Int.floor (q i * (n + 1 : ℝ))

private lemma measurable_gridVec {d : ℕ} (n : ℕ) : Measurable (gridVec (d := d) n) := by
  refine measurable_pi_lambda _ ?_
  intro i
  simpa [gridVec] using
    (Int.measurable_floor.comp ((measurable_pi_apply i).mul measurable_const))

private def gridCube {d : ℕ} (n : ℕ) (v : Fin d → ℤ) : Set (Fin d → ℝ) :=
  gridVec (d := d) n ⁻¹' {v}

private lemma measurableSet_gridCube {d : ℕ} (n : ℕ) (v : Fin d → ℤ) :
    MeasurableSet (gridCube (d := d) n v) := by
  unfold gridCube
  exact measurable_gridVec (d := d) n (measurableSet_singleton v)

private noncomputable def gridAnchor {d : ℕ} (n : ℕ) (v : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (v i : ℝ) / (n + 1 : ℝ)

private noncomputable def gridStep {d : ℕ} (n : ℕ) (q : Fin d → ℝ) : Fin d → ℝ :=
  gridAnchor (d := d) n (gridVec (d := d) n q)

private lemma measurable_gridStep {d : ℕ} (n : ℕ) : Measurable (gridStep (d := d) n) := by
  refine measurable_pi_lambda _ ?_
  intro i
  have hcoord : Measurable fun q : Fin d → ℝ => (((gridVec (d := d) n q) i : ℤ) : ℝ) := by
    have hcoord_int : Measurable fun q : Fin d → ℝ => (gridVec (d := d) n q) i := by
      exact (measurable_pi_apply i).comp (measurable_gridVec (d := d) n)
    exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hcoord_int
  simpa [gridStep, gridAnchor] using hcoord.div_const (n + 1 : ℝ)

private lemma iUnion_gridCube_univ {d : ℕ} (n : ℕ) :
    (⋃ v : Fin d → ℤ, gridCube (d := d) n v) = Set.univ := by
  ext q
  simp [gridCube]

private lemma pairwise_disjoint_gridCube {d : ℕ} (n : ℕ) :
    Pairwise (Function.onFun Disjoint (gridCube (d := d) n)) := by
  intro v w hvw
  refine Set.disjoint_left.2 ?_
  intro q hqv hqw
  have hv : gridVec (d := d) n q = v := by
    simpa [gridCube] using hqv
  have hw : gridVec (d := d) n q = w := by
    simpa [gridCube] using hqw
  exact hvw (hv.symm.trans hw)

private lemma abs_sub_gridStep_coord_lt_one {d : ℕ} (n : ℕ) (q : Fin d → ℝ) (i : Fin d) :
    |gridStep (d := d) n q i - q i| < 1 := by
  let z : ℤ := gridVec (d := d) n q i
  have hfloor1 : (z : ℝ) ≤ q i * (n + 1 : ℝ) := by
    simpa [z, gridVec] using (Int.floor_le (q i * (n + 1 : ℝ)))
  have hfloor2 : q i * (n + 1 : ℝ) < z + 1 := by
    simpa [z, gridVec] using (Int.lt_floor_add_one (q i * (n + 1 : ℝ)))
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hleft : (z : ℝ) / (n + 1 : ℝ) ≤ q i := by
    exact (div_le_iff₀ hpos).2 hfloor1
  have hright : q i < (z : ℝ) / (n + 1 : ℝ) + 1 := by
    have : q i < (z + 1) / (n + 1 : ℝ) := by
      exact (lt_div_iff₀ hpos).2 hfloor2
    have hbound : (z + 1) / (n + 1 : ℝ) ≤ (z : ℝ) / (n + 1 : ℝ) + 1 := by
      have hone : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
        exact (div_le_iff₀ hpos).2 (by nlinarith)
      calc
        (z + 1) / (n + 1 : ℝ) = (z : ℝ) / (n + 1 : ℝ) + (1 : ℝ) / (n + 1 : ℝ) := by ring
        _ ≤ (z : ℝ) / (n + 1 : ℝ) + 1 := by gcongr
    exact lt_of_lt_of_le this hbound
  have hanchor : gridStep (d := d) n q i = (z : ℝ) / (n + 1 : ℝ) := by
    simp [gridStep, gridAnchor, z]
  rw [hanchor]
  have hle : (z : ℝ) / (n + 1 : ℝ) - q i ≤ 0 := by linarith
  rw [abs_lt]
  constructor <;> linarith

private lemma abs_sub_gridStep_coord_lt_inv {d : ℕ} (n : ℕ) (q : Fin d → ℝ) (i : Fin d) :
    |gridStep (d := d) n q i - q i| < 1 / (n + 1 : ℝ) := by
  let z : ℤ := gridVec (d := d) n q i
  have hfloor1 : (z : ℝ) ≤ q i * (n + 1 : ℝ) := by
    simpa [z, gridVec] using (Int.floor_le (q i * (n + 1 : ℝ)))
  have hfloor2 : q i * (n + 1 : ℝ) < z + 1 := by
    simpa [z, gridVec] using (Int.lt_floor_add_one (q i * (n + 1 : ℝ)))
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hanchor : gridStep (d := d) n q i = (z : ℝ) / (n + 1 : ℝ) := by
    simp [gridStep, gridAnchor, z]
  have hright : (z : ℝ) / (n + 1 : ℝ) ≤ q i := by
    exact (div_le_iff₀ hpos).2 hfloor1
  have hleft : q i < (z : ℝ) / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) := by
    have htmp : q i < ((z : ℝ) + 1) / (n + 1 : ℝ) := by
      exact (lt_div_iff₀ hpos).2 hfloor2
    have heq : ((z : ℝ) + 1) / (n + 1 : ℝ) =
        (z : ℝ) / (n + 1 : ℝ) + 1 / (n + 1 : ℝ) := by
      ring
    simpa [heq] using htmp
  rw [hanchor, abs_lt]
  constructor <;> linarith

private lemma abs_sub_gridStep_coord_le_inv {d : ℕ} (n : ℕ) (q : Fin d → ℝ) (i : Fin d) :
    |gridStep (d := d) n q i - q i| ≤ 1 / (n + 1 : ℝ) :=
  (abs_sub_gridStep_coord_lt_inv (d := d) n q i).le

private lemma norm_sub_gridStep_lt_one {d : ℕ} (n : ℕ) (q : Fin d → ℝ) :
    ‖gridStep (d := d) n q - q‖ < 1 := by
  refine (pi_norm_lt_iff (x := gridStep (d := d) n q - q) zero_lt_one).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using abs_sub_gridStep_coord_lt_one (d := d) n q i

private lemma norm_sub_gridStep_lt_inv {d : ℕ} (n : ℕ) (q : Fin d → ℝ) :
    ‖gridStep (d := d) n q - q‖ < 1 / (n + 1 : ℝ) := by
  have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by
    have : (0 : ℝ) < n + 1 := by positivity
    exact one_div_pos.mpr this
  refine (pi_norm_lt_iff (x := gridStep (d := d) n q - q) hpos).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using abs_sub_gridStep_coord_lt_inv (d := d) n q i

private lemma tendsto_gridStep {d : ℕ} (q : Fin d → ℝ) :
    Tendsto (fun n : ℕ => gridStep (d := d) n q) atTop (nhds q) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  rcases Metric.tendsto_atTop.1
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0))
      ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hsmall : 1 / (n + 1 : ℝ) < ε := by
    have habs : |((n : ℝ) + 1)| = (n : ℝ) + 1 := by
      exact abs_of_nonneg (by positivity)
    simpa [one_div, habs] using hN n hn
  rw [dist_eq_norm]
  exact lt_trans (norm_sub_gridStep_lt_inv (d := d) n q) hsmall

private lemma mem_closedBall_gridStep_of_mem_closedBall {d : ℕ} (n : ℕ) {q : Fin d → ℝ}
    {R : ℝ} (hq : q ∈ Metric.closedBall (0 : Fin d → ℝ) R) :
    gridStep (d := d) n q ∈ Metric.closedBall (0 : Fin d → ℝ) (R + 1) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hq ⊢
  have hq' : ‖q‖ ≤ R := by simpa using hq
  have htriangle : ‖gridStep (d := d) n q‖ ≤ ‖gridStep (d := d) n q - q‖ + ‖q‖ := by
    calc
      ‖gridStep (d := d) n q‖ = ‖(gridStep (d := d) n q - q) + q‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖gridStep (d := d) n q - q‖ + ‖q‖ := norm_add_le _ _
  have hstep : ‖gridStep (d := d) n q - q‖ < 1 := norm_sub_gridStep_lt_one (d := d) n q
  have hbound : ‖gridStep (d := d) n q‖ < R + 1 := by
    nlinarith [htriangle, hstep, hq']
  simpa using hbound.le

private lemma gridCube_subset_closedBall_compl_of_anchor_closedBall_compl {d : ℕ} (n : ℕ)
    (v : Fin d → ℤ) {R : ℝ}
    (hv : gridAnchor (d := d) n v ∈ (Metric.closedBall (0 : Fin d → ℝ) (R + 1))ᶜ) :
    gridCube (d := d) n v ⊆ (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ := by
  intro q hq
  by_contra hqR
  have hq_ball : q ∈ Metric.closedBall (0 : Fin d → ℝ) R := by
    simpa using hqR
  have hstep_ball :
      gridStep (d := d) n q ∈ Metric.closedBall (0 : Fin d → ℝ) (R + 1) :=
    mem_closedBall_gridStep_of_mem_closedBall (d := d) n hq_ball
  have hvec : gridVec (d := d) n q = v := by
    simpa [gridCube] using hq
  have hstep_eq : gridStep (d := d) n q = gridAnchor (d := d) n v := by
    simp [gridStep, hvec]
  exact hv (hstep_eq ▸ hstep_ball)

private def codedGridCube {d : ℕ} (n k : ℕ) : Set (Fin d → ℝ) :=
  ⋃ v ∈ Encodable.decode₂ (Fin d → ℤ) k, gridCube (d := d) n v

private lemma measurableSet_codedGridCube {d : ℕ} (n k : ℕ) :
    MeasurableSet (codedGridCube (d := d) n k) := by
  dsimp [codedGridCube]
  exact Encodable.iUnion_decode₂_cases
    (C := MeasurableSet) MeasurableSet.empty (fun v => measurableSet_gridCube (d := d) n v)

private lemma iUnion_codedGridCube_univ {d : ℕ} (n : ℕ) :
    (⋃ k : ℕ, codedGridCube (d := d) n k) = Set.univ := by
  simpa [codedGridCube] using
    (Encodable.iUnion_decode₂ (f := fun v : Fin d → ℤ => gridCube (d := d) n v)).trans
      (iUnion_gridCube_univ (d := d) n)

private lemma pairwise_disjoint_codedGridCube {d : ℕ} (n : ℕ) :
    Pairwise (Function.onFun Disjoint (codedGridCube (d := d) n)) := by
  simpa [codedGridCube] using
    (Encodable.iUnion_decode₂_disjoint_on
      (f := fun v : Fin d → ℤ => gridCube (d := d) n v)
      (pairwise_disjoint_gridCube (d := d) n))

private noncomputable def jointApproxMeasure {d : ℕ} (n : ℕ)
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ) :
    Measure (ℝ × (Fin d → ℝ)) :=
  Measure.sum fun v : Fin d → ℤ =>
    (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩).prod
      (Measure.dirac (gridAnchor (d := d) n v))

private lemma jointApproxMeasure_univ {d : ℕ} (n : ℕ)
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ)
    (ν0 : Measure (Fin d → ℝ))
    (hσmass0 : ∀ B : {B : Set (Fin d → ℝ) // MeasurableSet B}, (σ B) Set.univ = ν0 B.1) :
    jointApproxMeasure (d := d) n σ Set.univ = ν0 Set.univ := by
  rw [jointApproxMeasure, Measure.sum_apply _ MeasurableSet.univ]
  calc
    ∑' v : Fin d → ℤ,
        ((σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩).prod
          (Measure.dirac (gridAnchor (d := d) n v))) Set.univ
      = ∑' v : Fin d → ℤ,
          (σ ⟨gridCube (d := d) n v,
            measurableSet_gridCube (d := d) n v⟩) Set.univ := by
          congr with v
          rw [← univ_prod_univ, Measure.prod_prod]
          simp
    _ = ∑' v : Fin d → ℤ, ν0 (gridCube (d := d) n v) := by
          congr with v
          exact hσmass0 ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩
    _ = ν0 Set.univ := by
          rw [← iUnion_gridCube_univ (d := d) n, MeasureTheory.measure_iUnion
            (pairwise_disjoint_gridCube (d := d) n) (measurableSet_gridCube (d := d) n)]

private lemma jointApproxMeasure_univ_prod_closedBall_compl_le {d : ℕ} (n : ℕ)
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ)
    (ν0 : Measure (Fin d → ℝ))
    (hσmass0 : ∀ B : {B : Set (Fin d → ℝ) // MeasurableSet B}, (σ B) Set.univ = ν0 B.1)
    (R : ℝ) :
    jointApproxMeasure (d := d) n σ (Set.univ.prod (Metric.closedBall (0 : Fin d → ℝ) (R + 1))ᶜ) ≤
      ν0 (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ := by
  let S : Set (Fin d → ℝ) := (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ
  let T : Set (Fin d → ℝ) := (Metric.closedBall (0 : Fin d → ℝ) (R + 1))ᶜ
  change (Measure.sum fun v : Fin d → ℤ =>
      (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩).prod
        (Measure.dirac (gridAnchor (d := d) n v))) (Set.univ ×ˢ T) ≤ ν0 S
  rw [Measure.sum_apply _ (MeasurableSet.univ.prod
    (Metric.isClosed_closedBall.measurableSet.compl))]
  calc
    ∑' v : Fin d → ℤ,
        ((σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩).prod
          (Measure.dirac (gridAnchor (d := d) n v))) (Set.univ ×ˢ T)
      ≤ ∑' v : Fin d → ℤ, ν0 (gridCube (d := d) n v ∩ S) := by
          refine ENNReal.tsum_le_tsum ?_
          intro v
          by_cases hv : gridAnchor (d := d) n v ∈ T
          · have hsubset : gridCube (d := d) n v ⊆ S :=
              gridCube_subset_closedBall_compl_of_anchor_closedBall_compl (d := d) n v hv
            have hEq : ν0 (gridCube (d := d) n v) = ν0 (gridCube (d := d) n v ∩ S) := by
              rw [inter_eq_left.2 hsubset]
            rw [Measure.prod_prod]
            simp [T, hv, hσmass0, hEq]
          · rw [Measure.prod_prod]
            simp [T, hv]
    _ = ν0 S := by
          have hUnion : (⋃ v : Fin d → ℤ, gridCube (d := d) n v ∩ S) = S := by
            ext q
            constructor
            · intro hq
              simp only [Set.mem_iUnion, Set.mem_inter_iff] at hq
              exact hq.choose_spec.2
            · intro hq
              refine Set.mem_iUnion.2 ⟨gridVec (d := d) n q, ?_⟩
              simp [gridCube, hq]
          have hdisj : Pairwise (Function.onFun Disjoint
              fun v : Fin d → ℤ =>
                gridCube (d := d) n v ∩ S) := by
            intro v w hvw
            refine Set.disjoint_left.2 ?_
            intro q hqv hqw
            exact (pairwise_disjoint_gridCube (d := d) n hvw).le_bot ⟨hqv.1, hqw.1⟩
          have hsum :
              ν0 (⋃ v : Fin d → ℤ, gridCube (d := d) n v ∩ S) =
                ∑' v : Fin d → ℤ, ν0 (gridCube (d := d) n v ∩ S) := by
            rw [MeasureTheory.measure_iUnion hdisj]
            intro v
            exact (measurableSet_gridCube (d := d) n v).inter
              Metric.isClosed_closedBall.measurableSet.compl
          calc
            ∑' v : Fin d → ℤ, ν0 (gridCube (d := d) n v ∩ S)
              = ν0 (⋃ v : Fin d → ℤ, gridCube (d := d) n v ∩ S) := hsum.symm
            _ = ν0 S := by rw [hUnion]

private lemma jointApproxMeasure_Iio_prod_univ {d : ℕ} (n : ℕ)
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ)
    (hσsupp : ∀ B, σ B (Set.Iio 0) = 0) :
    jointApproxMeasure (d := d) n σ ((Set.Iio 0).prod Set.univ) = 0 := by
  change (Measure.sum fun v : Fin d → ℤ =>
      (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩).prod
        (Measure.dirac (gridAnchor (d := d) n v))) ((Set.Iio 0) ×ˢ Set.univ) = 0
  rw [Measure.sum_apply _ (measurableSet_Iio.prod MeasurableSet.univ)]
  simp_rw [Measure.prod_prod, hσsupp, zero_mul]
  simp

private lemma jointApproxMeasure_ae_nonneg_fst {d : ℕ} (n : ℕ)
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ)
    (hσsupp : ∀ B, σ B (Set.Iio 0) = 0) :
    ∀ᵐ z ∂(jointApproxMeasure (d := d) n σ), 0 ≤ z.1 := by
  rw [ae_iff]
  have hset : {a : ℝ × (Fin d → ℝ) | ¬ 0 ≤ a.1} = (Set.Iio 0).prod Set.univ := by
    ext z
    constructor
    · intro hz
      exact ⟨lt_of_not_ge hz, Set.mem_univ _⟩
    · intro hz
      exact not_le_of_gt hz.1
  rw [hset]
  exact jointApproxMeasure_Iio_prod_univ (d := d) n σ hσsupp

private lemma jointApproxMeasure_integrable_kernel {d : ℕ} (n : ℕ)
    (ν0 : Measure (Fin d → ℝ)) [IsFiniteMeasure ν0]
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ)
    (hσmass0 : ∀ B : {B : Set (Fin d → ℝ) // MeasurableSet B}, (σ B) Set.univ = ν0 B.1)
    (hσsupp : ∀ B, σ B (Set.Iio 0) = 0)
    {t : ℝ} (ht : 0 ≤ t) (a : Fin d → ℝ) :
    Integrable
      (fun z : ℝ × (Fin d → ℝ) =>
        exp (-(↑(t * z.1) : ℂ)) *
          exp (I * ↑(∑ i : Fin d, z.2 i * a i)))
      (jointApproxMeasure (d := d) n σ) := by
  haveI : IsFiniteMeasure (jointApproxMeasure (d := d) n σ) := by
    refine ⟨?_⟩
    rw [jointApproxMeasure_univ (d := d) n σ ν0 hσmass0]
    exact measure_lt_top ν0 Set.univ
  refine MeasureTheory.Integrable.mono'
    (μ := jointApproxMeasure (d := d) n σ)
    (f := fun z : ℝ × (Fin d → ℝ) =>
      exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)))
    (g := fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ))
    (integrable_const (1 : ℝ)) ?_ ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · have h_nonneg :
        ∀ᵐ z ∂(jointApproxMeasure (d := d) n σ), 0 ≤ z.1 :=
      jointApproxMeasure_ae_nonneg_fst (d := d) n σ hσsupp
    filter_upwards [h_nonneg] with z hz
    have hle : Real.exp (-(t * z.1)) ≤ 1 := by
      apply (Real.exp_le_one_iff).2
      nlinarith [mul_nonneg ht hz]
    calc
      ‖exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i))‖
          = ‖exp (-(↑(t * z.1) : ℂ))‖ *
              ‖exp (I * ↑(∑ i : Fin d, z.2 i * a i))‖ := norm_mul _ _
      _ = Real.exp (-(t * z.1)) * 1 := by
            simp [Complex.norm_exp]
      _ ≤ 1 := by nlinarith

private lemma jointApproxMeasure_integral_kernel {d : ℕ} (n : ℕ)
    (ν : ℝ → Measure (Fin d → ℝ))
    (ν0 : Measure (Fin d → ℝ)) [IsFiniteMeasure ν0]
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ)
    (hσfin : ∀ B, IsFiniteMeasure (σ B))
    (hσmass0 : ∀ B : {B : Set (Fin d → ℝ) // MeasurableSet B}, (σ B) Set.univ = ν0 B.1)
    (hσsupp : ∀ B, σ B (Set.Iio 0) = 0)
    (hσlaplace : ∀ B t, 0 ≤ t → ((ν t) B.1).toReal = ∫ p, Real.exp (-(t * p)) ∂(σ B))
    (t : ℝ) (a : Fin d → ℝ) (ht : 0 ≤ t) :
    ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i))
      ∂(jointApproxMeasure (d := d) n σ)
      = ∑' v : Fin d → ℤ,
          (((ν t) (gridCube (d := d) n v)).toReal : ℂ) *
            exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) := by
  rw [jointApproxMeasure, integral_sum_measure
    (jointApproxMeasure_integrable_kernel (d := d) n ν0 σ hσmass0 hσsupp ht a)]
  congr with v
  haveI : IsFiniteMeasure (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩) :=
    hσfin ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩
  have hreal :
      ∫ p, exp (-(↑(t * p) : ℂ))
          ∂(σ ⟨gridCube (d := d) n v,
              measurableSet_gridCube (d := d) n v⟩)
        = ↑(∫ p, Real.exp (-(t * p))
            ∂(σ ⟨gridCube (d := d) n v,
                measurableSet_gridCube (d := d) n v⟩)) := by
    have hcongr :
        (fun p : ℝ => exp (-(↑(t * p) : ℂ))) =
          fun p : ℝ => ((Real.exp (-(t * p)) : ℝ) : ℂ) := by
      funext p
      simp
    rw [hcongr, integral_complex_ofReal]
  calc
    ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i))
        ∂(σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩).prod
          (Measure.dirac (gridAnchor (d := d) n v))
      = (∫ p, exp (-(↑(t * p) : ℂ))
            ∂(σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩)) *
          ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i))
            ∂(Measure.dirac (gridAnchor (d := d) n v)) := by
            simpa using
              (integral_prod_mul
                (μ := σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩)
                (ν := Measure.dirac (gridAnchor (d := d) n v))
                (f := fun p : ℝ => exp (-(↑(t * p) : ℂ)))
                (g := fun q : Fin d → ℝ => exp (I * ↑(∑ i : Fin d, q i * a i))))
    _ = (∫ p, exp (-(↑(t * p) : ℂ))
            ∂(σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩)) *
          exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) := by
            rw [integral_dirac]
    _ = (((ν t) (gridCube (d := d) n v)).toReal : ℂ) *
          exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) := by
            rw [hreal]
            congr 1
            symm
            exact congrArg Complex.ofReal
              (hσlaplace ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩ t ht)

private lemma normalize_le_prod {d : ℕ}
    (μ : FiniteMeasure (ℝ × (Fin d → ℝ))) (hμ : μ ≠ 0)
    (hm : 1 ≤ μ.mass) (A : Set (ℝ × (Fin d → ℝ))) :
    ((μ.normalize : ProbabilityMeasure (ℝ × (Fin d → ℝ))) : Measure (ℝ × (Fin d → ℝ))) A ≤
      ((μ : FiniteMeasure (ℝ × (Fin d → ℝ))) : Measure (ℝ × (Fin d → ℝ))) A := by
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero μ hμ, Measure.smul_apply]
  change (↑(μ.mass⁻¹) : ENNReal) * (((μ : FiniteMeasure (ℝ × (Fin d → ℝ))) :
    Measure (ℝ × (Fin d → ℝ))) A) ≤
      (((μ : FiniteMeasure (ℝ × (Fin d → ℝ))) : Measure (ℝ × (Fin d → ℝ))) A)
  exact mul_le_of_le_one_left (zero_le _)
    (ENNReal.coe_le_coe.mpr (inv_le_one_of_one_le₀ hm))

private lemma integral_gridStep_char_eq_tsum {d : ℕ}
    (ν : ℝ → Measure (Fin d → ℝ)) (t : ℝ) (a : Fin d → ℝ) (n : ℕ)
    [IsFiniteMeasure (ν t)] :
    ∫ q, exp (I * ↑(∑ i : Fin d, gridStep (d := d) n q i * a i)) ∂(ν t)
      = ∑' v : Fin d → ℤ,
          (((ν t) (gridCube (d := d) n v)).toReal : ℂ) *
            exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) := by
  let f : (Fin d → ℝ) → ℂ := fun q =>
    exp (I * ↑(∑ i : Fin d, gridStep (d := d) n q i * a i))
  have hf_meas : Measurable f := by
    apply Measurable.cexp
    apply Measurable.mul measurable_const
    exact Complex.continuous_ofReal.measurable.comp <| by
      simpa using
        (Finset.measurable_sum Finset.univ fun i _ =>
          Measurable.mul
            (measurable_pi_apply i |>.comp (measurable_gridStep (d := d) n))
            measurable_const)
  have hf_int : Integrable f (ν t) := by
    refine MeasureTheory.Integrable.mono' (integrable_const (1 : ℝ)) hf_meas.aestronglyMeasurable ?_
    filter_upwards with q
    have hnorm : ‖f q‖ = 1 := by
      have h_re : (I * ↑(∑ i : Fin d, gridStep (d := d) n q i * a i) : ℂ).re = 0 := by simp
      calc
        ‖f q‖ = Real.exp ((I * ↑(∑ i : Fin d, gridStep (d := d) n q i * a i) : ℂ).re) := by
          simp [f, Complex.norm_exp]
        _ = 1 := by rw [h_re]; norm_num
    linarith
  have huniv : (⋃ v : Fin d → ℤ, gridCube (d := d) n v) = Set.univ :=
    iUnion_gridCube_univ (d := d) n
  have hdisj : Pairwise (Function.onFun Disjoint (gridCube (d := d) n)) :=
    pairwise_disjoint_gridCube (d := d) n
  have hmeas : ∀ v, MeasurableSet (gridCube (d := d) n v) := fun v =>
    measurableSet_gridCube (d := d) n v
  rw [← MeasureTheory.setIntegral_univ, ← huniv]
  rw [MeasureTheory.integral_iUnion hmeas hdisj hf_int.integrableOn]
  apply tsum_congr
  intro v
  have h_eq : ∀ q ∈ gridCube (d := d) n v,
      f q = exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) := by
    intro q hq
    have hq_vec : gridVec (d := d) n q = v := by simpa [gridCube] using hq
    have h_step : gridStep (d := d) n q = gridAnchor (d := d) n v := by
      ext i
      simp [gridStep, gridAnchor, hq_vec]
    dsimp [f]
    rw [h_step]
  rw [MeasureTheory.setIntegral_congr_fun (hmeas v) h_eq, MeasureTheory.setIntegral_const]
  exact show ((ν t) (gridCube (d := d) n v)).toReal •
      exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) =
    (((ν t) (gridCube (d := d) n v)).toReal : ℂ) *
      exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) by
    simp

private noncomputable def laplaceCharBCF {d : ℕ} (t : ℝ) (ht : 0 ≤ t) (a : Fin d → ℝ) :
    BoundedContinuousFunction (ℝ × (Fin d → ℝ)) ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => exp (-(↑(t * max z.1 0) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)), by
      apply Continuous.mul
      · apply Continuous.cexp
        apply Continuous.neg
        apply Complex.continuous_ofReal.comp
        apply Continuous.mul continuous_const
        exact (continuous_fst.max continuous_const)
      · apply Continuous.cexp
        apply Continuous.mul continuous_const
        apply Complex.continuous_ofReal.comp
        apply continuous_finset_sum _
          (fun i _ =>
            (continuous_apply i |>.comp continuous_snd).mul
              continuous_const)⟩
    2
    (by
      intro z y
      set fz : ℂ := exp (-(↑(t * max z.1 0) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i))
      set fy : ℂ := exp (-(↑(t * max y.1 0) : ℂ)) * exp (I * ↑(∑ i : Fin d, y.2 i * a i))
      rw [dist_eq_norm]
      change ‖fz - fy‖ ≤ 2
      have hfz : ‖fz‖ ≤ 1 := by
        dsimp [fz]
        rw [norm_mul]
        have h1 : ‖exp (-(↑(t * max z.1 0) : ℂ))‖ = Real.exp (-(t * max z.1 0)) := by
          simp [Complex.norm_exp]
        have h2 : ‖exp (I * ↑(∑ i : Fin d, z.2 i * a i))‖ = 1 := by
          simpa [mul_comm] using (Complex.norm_exp_ofReal_mul_I (∑ i : Fin d, z.2 i * a i))
        rw [h1, h2, mul_one]
        apply (Real.exp_le_one_iff).2
        have hmax : 0 ≤ max z.1 0 := le_max_right _ _
        exact neg_nonpos.mpr (mul_nonneg ht hmax)
      have hfy : ‖fy‖ ≤ 1 := by
        dsimp [fy]
        rw [norm_mul]
        have h1 : ‖exp (-(↑(t * max y.1 0) : ℂ))‖ = Real.exp (-(t * max y.1 0)) := by
          simp [Complex.norm_exp]
        have h2 : ‖exp (I * ↑(∑ i : Fin d, y.2 i * a i))‖ = 1 := by
          simpa [mul_comm] using (Complex.norm_exp_ofReal_mul_I (∑ i : Fin d, y.2 i * a i))
        rw [h1, h2, mul_one]
        apply (Real.exp_le_one_iff).2
        have hmax : 0 ≤ max y.1 0 := le_max_right _ _
        exact neg_nonpos.mpr (mul_nonneg ht hmax)
      calc
        ‖fz - fy‖ ≤ ‖fz‖ + ‖fy‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hfz hfy
        _ = 2 := by norm_num)

private lemma integral_laplaceCharBCF_eq {d : ℕ} {μ : Measure (ℝ × (Fin d → ℝ))}
    (hsupp : μ ((Set.Iio 0).prod Set.univ) = 0)
    (t : ℝ) (ht : 0 ≤ t) (a : Fin d → ℝ) :
    ∫ z, laplaceCharBCF (d := d) t ht a z ∂μ
      = ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)) ∂μ := by
  have h_nonneg : ∀ᵐ z ∂μ, 0 ≤ z.1 := by
    have hset : {z : ℝ × (Fin d → ℝ) | z.1 < 0} = ((Set.Iio 0).prod Set.univ) := by
      ext z
      constructor
      · intro hz
        exact ⟨hz, trivial⟩
      · intro hz
        exact hz.1
    rw [ae_iff]
    simpa [not_le, hset] using hsupp
  apply MeasureTheory.integral_congr_ae
  filter_upwards [h_nonneg] with z hz0
  simp [laplaceCharBCF, max_eq_left hz0]

/-- Assembly of a joint measure from an already-constructed temporal slice family.

This is the remaining measure-theoretic extension step after slice existence,
support, and countable additivity have been formalized in this file.

**Proof sketch (bimeasure extension).**
We are given a family `σ(B)` of finite measures on `ℝ`, indexed by measurable
`B ⊆ ℝ^d`, that is countably additive in `B` (hypothesis `hσiUnion`).

*Step 1 — Spatial slices.*  For each measurable `A ⊆ ℝ`, define
`τ_A(B) := σ(B)(A)`.  By `hσiUnion`, `τ_A` is countably additive in `B`,
so `τ_A` is a finite measure on `ℝ^d` (via `Measure.ofMeasurable`).
Moreover `A ↦ τ_A(B) = σ(B)(A)` is a measure (namely `σ(B)`).

*Step 2 — Product extension.*  The pair `(A, B) ↦ σ(B)(A)` is a
bimeasure — separately countably additive in each variable — and bounded
by `σ(Set.univ)(ℝ) < ∞`.  By the Kingman–Carathéodory bimeasure extension
theorem for finite bimeasures on standard Borel spaces, there exists a
unique finite measure `μ` on `ℝ × ℝ^d` with `μ(A × B) = σ(B)(A)`.

*Step 3 — Fourier-Laplace identity.*  The integral identity follows from
the Laplace representation of each slice `σ(B)` and the Bochner
representation of each `ν(t)`, combined with Fubini on the joint measure.

The bimeasure extension (Step 2) is not currently in Mathlib; the
construction below uses `sorry` for this step.  This is strictly stronger
than the former `axiom` status since the remaining gap is a well-known
measure-theoretic result, not a domain-specific claim. -/
theorem joint_measure_from_temporal_slices {d : ℕ}
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ)
    (hσfin : ∀ B, IsFiniteMeasure (σ B))
    (hσsupp : ∀ B, σ B (Set.Iio 0) = 0)
    (hσlaplace : ∀ B t, 0 ≤ t → ((ν t) B.1).toReal = ∫ p, Real.exp (-(t * p)) ∂(σ B))
    (hσiUnion : ∀ (B : ℕ → Set (Fin d → ℝ)) (hB : ∀ n, MeasurableSet (B n))
      (_hdisj : Pairwise (Function.onFun Disjoint B)),
      σ ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩ =
        Measure.sum (fun n => σ ⟨B n, hB n⟩)) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ ((Set.Iio 0).prod Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        (∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t)) =
          ∫ p : ℝ × (Fin d → ℝ),
            exp (-(↑(t * p.1) : ℂ)) *
              exp (I * ↑(∑ i : Fin d, p.2 i * a i))
            ∂μ := by
  let ν0 : Measure (Fin d → ℝ) := ν 0
  haveI hν0 : IsFiniteMeasure ν0 := hν 0 le_rfl
  have hσmass0 : ∀ B : {B : Set (Fin d → ℝ) // MeasurableSet B}, (σ B) Set.univ = ν0 B.1 := by
    intro B
    have h0 := hσlaplace B 0 le_rfl
    have hνtop : ν0 B.1 ≠ ⊤ := measure_ne_top ν0 B.1
    have hσtop : (σ B) Set.univ ≠ ⊤ := measure_ne_top (σ B) Set.univ
    have h0' : (ν0 B.1).toReal = ((σ B) Set.univ).toReal := by
      simpa [ν0, Measure.real] using h0
    exact ((ENNReal.toReal_eq_toReal_iff' hνtop hσtop).mp h0').symm
  let μn : ℕ → Measure (ℝ × (Fin d → ℝ)) := fun n =>
    jointApproxMeasure (d := d) n σ
  have hμn_fin : ∀ n, IsFiniteMeasure (μn n) := by
    intro n
    dsimp [μn]
    refine ⟨?_⟩
    rw [jointApproxMeasure_univ (d := d) n σ ν0 hσmass0]
    exact measure_lt_top ν0 Set.univ
  have hμn_supp : ∀ n, μn n ((Set.Iio 0).prod Set.univ) = 0 := by
    intro n
    dsimp [μn]
    exact jointApproxMeasure_Iio_prod_univ (d := d) n σ hσsupp
  have hμn_repr :
      ∀ n (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        ∫ p : ℝ × (Fin d → ℝ),
            exp (-(↑(t * p.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂(μn n)
          = ∑' v : Fin d → ℤ,
              (((ν t) (gridCube (d := d) n v)).toReal : ℂ) *
                exp (I * ↑(∑ i : Fin d, gridAnchor (d := d) n v i * a i)) := by
    intro n t a ht
    dsimp [μn]
    exact jointApproxMeasure_integral_kernel (d := d) n ν ν0 σ hσfin hσmass0 hσsupp hσlaplace t a ht
  have hμn_p_tail :
      ∀ n K, μn n ((Set.Ioi K).prod Set.univ) = (σ ⟨Set.univ, MeasurableSet.univ⟩) (Set.Ioi K) := by
    intro n K
    let c : ℕ → Set (Fin d → ℝ) := codedGridCube (d := d) n
    have hσsum_nat :
        σ ⟨Set.univ, MeasurableSet.univ⟩ =
          Measure.sum (fun k => σ ⟨c k, measurableSet_codedGridCube (d := d) n k⟩) := by
      simpa [c, iUnion_codedGridCube_univ (d := d) n] using
        hσiUnion c (fun k => measurableSet_codedGridCube (d := d) n k)
          (pairwise_disjoint_codedGridCube (d := d) n)
    have happly :
        (σ ⟨Set.univ, MeasurableSet.univ⟩) (Set.Ioi K) =
          ∑' k : ℕ, (σ ⟨c k, measurableSet_codedGridCube (d := d) n k⟩) (Set.Ioi K) := by
      simpa [Measure.sum_apply_of_countable] using
        congrArg (fun μ : Measure ℝ => μ (Set.Ioi K)) hσsum_nat
    have hreindex :
        ∑' k : ℕ, (σ ⟨c k, measurableSet_codedGridCube (d := d) n k⟩) (Set.Ioi K)
          = ∑' v : Fin d → ℤ,
              (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩) (Set.Ioi K) := by
      classical
      let m : Set (Fin d → ℝ) → ENNReal := fun s =>
        if hs : MeasurableSet s then (σ ⟨s, hs⟩) (Set.Ioi K) else 0
      have hm0 : m ∅ = 0 := by
        have hempty_univ : (σ ⟨∅, MeasurableSet.empty⟩) Set.univ = 0 := by
          simpa using hσmass0 ⟨∅, MeasurableSet.empty⟩
        have hzero : (σ ⟨∅, MeasurableSet.empty⟩) (Set.Ioi K) = 0 := by
          refine le_antisymm ?_ (zero_le _)
          have hmono :
              (σ ⟨∅, MeasurableSet.empty⟩) (Set.Ioi K) ≤ (σ ⟨∅, MeasurableSet.empty⟩) Set.univ :=
            measure_mono (by intro x hx; simp)
          rw [hempty_univ] at hmono
          exact hmono
        simpa [m] using hzero
      have hcoded :
          ∀ k : ℕ, m (codedGridCube (d := d) n k) =
            (σ ⟨c k, measurableSet_codedGridCube (d := d) n k⟩) (Set.Ioi K) := by
        intro k
        dsimp [m]
        rw [dif_pos (measurableSet_codedGridCube (d := d) n k)]
      have hgrid :
          ∀ v : Fin d → ℤ, m (gridCube (d := d) n v) =
            (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩) (Set.Ioi K) := by
        intro v
        dsimp [m]
        rw [dif_pos (measurableSet_gridCube (d := d) n v)]
      calc
        ∑' k : ℕ, (σ ⟨c k, measurableSet_codedGridCube (d := d) n k⟩) (Set.Ioi K)
          = ∑' k : ℕ, m (codedGridCube (d := d) n k) := by
              congr with k
              symm
              exact hcoded k
        _ = ∑' v : Fin d → ℤ, m (gridCube (d := d) n v) := by
              simpa [codedGridCube] using
                (tsum_iUnion_decode₂ m hm0 (fun v : Fin d → ℤ => gridCube (d := d) n v))
        _ = ∑' v : Fin d → ℤ,
              (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩) (Set.Ioi K) := by
              congr with v
              exact hgrid v
    have hprod :
        μn n ((Set.Ioi K).prod Set.univ)
          = ∑' v : Fin d → ℤ,
              (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩) (Set.Ioi K) := by
      dsimp [μn, jointApproxMeasure]
      rw [Measure.sum_apply_of_countable]
      congr with v
      calc
        ((σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩).prod
            (Measure.dirac (gridAnchor (d := d) n v))) ((Set.Ioi K).prod Set.univ)
            = (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩) (Set.Ioi K) *
                (Measure.dirac (gridAnchor (d := d) n v)) Set.univ := by
                  rw [show ((Set.Ioi K).prod (Set.univ : Set (Fin d → ℝ))) =
                      (Set.Ioi K) ×ˢ (Set.univ : Set (Fin d → ℝ)) by rfl]
                  rw [Measure.prod_prod]
        _ = (σ ⟨gridCube (d := d) n v, measurableSet_gridCube (d := d) n v⟩) (Set.Ioi K) := by
              simp
    rw [hprod, ← hreindex]
    exact happly.symm
  let σuniv : Measure ℝ := σ ⟨Set.univ, MeasurableSet.univ⟩
  haveI hσuniv_fin : IsFiniteMeasure σuniv := hσfin ⟨Set.univ, MeasurableSet.univ⟩
  have hσuniv_ball :
      Tendsto (fun r : ℝ => σuniv (Metric.closedBall (0 : ℝ) r)ᶜ) atTop (nhds 0) := by
    simpa using
      (tendsto_measure_compl_closedBall_of_isTightMeasureSet
        (S := ({σuniv} : Set (Measure ℝ))) isTightMeasureSet_singleton 0)
  have hν0_ball :
      Tendsto (fun r : ℝ => ν0 (Metric.closedBall (0 : Fin d → ℝ) r)ᶜ) atTop (nhds 0) := by
    simpa using
      (tendsto_measure_compl_closedBall_of_isTightMeasureSet
        (S := ({ν0} : Set (Measure (Fin d → ℝ)))) isTightMeasureSet_singleton 0)
  have hμn_q_tail :
      ∀ n R, μn n (Set.univ.prod (Metric.closedBall (0 : Fin d → ℝ) (R + 1))ᶜ) ≤
        ν0 (Metric.closedBall (0 : Fin d → ℝ) R)ᶜ := by
    intro n R
    exact jointApproxMeasure_univ_prod_closedBall_compl_le (d := d) n σ ν0 hσmass0 R
  have htight :
      ∀ ε, 0 < ε →
        ∃ K R : ℝ, ∀ n,
          μn n ((((Set.Icc (-1) K).prod (Metric.closedBall (0 : Fin d → ℝ) (R + 1)))ᶜ)) ≤
            ENNReal.ofReal ε := by
    intro ε hε
    have hε2 : 0 < ENNReal.ofReal (ε / 2) := by positivity
    rw [ENNReal.tendsto_atTop_zero] at hσuniv_ball hν0_ball
    obtain ⟨K0, hK0⟩ := hσuniv_ball _ hε2
    obtain ⟨R0, hR0⟩ := hν0_ball _ hε2
    refine ⟨max K0 0, max R0 0, ?_⟩
    intro n
    have hKbound : σuniv (Set.Ioi (max K0 0)) ≤ ENNReal.ofReal (ε / 2) := by
      have hball :
          σuniv (Metric.closedBall (0 : ℝ) (max K0 0))ᶜ ≤ ENNReal.ofReal (ε / 2) :=
        hK0 _ (le_max_left _ _)
      refine le_trans (measure_mono ?_) hball
      intro x hx
      have hx0 : 0 ≤ x := le_trans (le_max_right K0 0) (le_of_lt hx)
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, Real.dist_eq]
      have habs : max K0 0 < |x - 0| := by simpa [sub_eq_add_neg, abs_of_nonneg hx0] using hx
      exact not_le.mpr habs
    have hRbound :
        ν0 (Metric.closedBall (0 : Fin d → ℝ) (max R0 0))ᶜ ≤ ENNReal.ofReal (ε / 2) :=
      hR0 _ (le_max_left _ _)
    have hsubset :
        (((Set.Icc (-1) (max K0 0)).prod
            (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1)))ᶜ : Set (ℝ × (Fin d → ℝ))) ⊆
          ((Set.Iio 0).prod Set.univ) ∪
            (((Set.Ioi (max K0 0)).prod Set.univ) ∪
              (Set.univ.prod (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1))ᶜ)) := by
      intro z hz
      rcases z with ⟨p, q⟩
      simp only [Set.mem_compl_iff] at hz
      by_cases hp0 : p < 0
      · exact Or.inl ⟨hp0, Set.mem_univ q⟩
      · have hp0' : 0 ≤ p := le_of_not_gt hp0
        by_cases hKp : max K0 0 < p
        · exact Or.inr (Or.inl ⟨hKp, Set.mem_univ q⟩)
        · have hpK : p ≤ max K0 0 := le_of_not_gt hKp
          have hq :
              q ∈ (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1))ᶜ := by
            intro hqball
            exact hz ⟨⟨by linarith, hpK⟩, hqball⟩
          exact Or.inr (Or.inr ⟨Set.mem_univ p, hq⟩)
    calc
      μn n ((((Set.Icc (-1) (max K0 0)).prod
          (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1)))ᶜ : Set (ℝ × (Fin d → ℝ))))
          ≤ μn n (((Set.Iio 0).prod Set.univ) ∪
              (((Set.Ioi (max K0 0)).prod Set.univ) ∪
                (Set.univ.prod (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1))ᶜ))) := by
              exact measure_mono hsubset
      _ ≤ μn n ((Set.Iio 0).prod Set.univ) +
            μn n (((Set.Ioi (max K0 0)).prod Set.univ) ∪
              (Set.univ.prod (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1))ᶜ)) := by
              exact measure_union_le _ _
      _ ≤ μn n ((Set.Iio 0).prod Set.univ) +
            (μn n ((Set.Ioi (max K0 0)).prod Set.univ) +
              μn n (Set.univ.prod (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1))ᶜ)) := by
              gcongr
              exact measure_union_le _ _
      _ = σuniv (Set.Ioi (max K0 0)) +
            μn n (Set.univ.prod (Metric.closedBall (0 : Fin d → ℝ) (max R0 0 + 1))ᶜ) := by
              rw [hμn_supp n, zero_add, hμn_p_tail n (max K0 0)]
      _ ≤ ENNReal.ofReal (ε / 2) + ν0 (Metric.closedBall (0 : Fin d → ℝ) (max R0 0))ᶜ := by
            gcongr
            exact hμn_q_tail n (max R0 0)
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
            gcongr
      _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            ring
  by_cases hmass0 : ν0 Set.univ = 0
  · refine ⟨0, by infer_instance, by simp, ?_⟩
    intro t a ht
    haveI := hν t ht
    have hσuniv_mass0 : σuniv Set.univ = 0 := by
      dsimp [σuniv]
      rw [hσmass0 ⟨Set.univ, MeasurableSet.univ⟩, hmass0]
    have hσuniv_zero : σuniv = 0 := by
      exact Measure.measure_univ_eq_zero.mp hσuniv_mass0
    have hνt_zero : ν t = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      have hreal0 : ((ν t) Set.univ).toReal = 0 := by
        simpa [σuniv, hσuniv_zero, Measure.real] using hσlaplace ⟨Set.univ, MeasurableSet.univ⟩ t ht
      rcases (ENNReal.toReal_eq_zero_iff _).mp hreal0 with hzero | htop
      · exact hzero
      · exact (measure_ne_top (ν t) Set.univ htop).elim
    simp [hνt_zero]
  · let Ω := ℝ × (Fin d → ℝ)
    let fμn : ℕ → FiniteMeasure Ω := fun n => ⟨μn n, hμn_fin n⟩
    let πn : ℕ → ProbabilityMeasure Ω := fun n => (fμn n).normalize
    let Mnn : NNReal := (fμn 0).mass
    have hMnn_ne : Mnn ≠ 0 := by
      intro hM0
      apply hmass0
      have hmass_enn : ((Mnn : NNReal) : ENNReal) = ν0 Set.univ := by
        dsimp [Mnn, fμn]
        rw [FiniteMeasure.ennreal_mass]
        simpa [μn] using jointApproxMeasure_univ (d := d) 0 σ ν0 hσmass0
      simpa [hM0] using hmass_enn.symm
    have hMnn_pos : 0 < (Mnn : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.2 hMnn_ne)
    have hmass_const : ∀ n, (fμn n).mass = Mnn := by
      intro n
      apply ENNReal.coe_injective
      have hmn : (((fμn n).mass : NNReal) : ENNReal) = ν0 Set.univ := by
        rw [FiniteMeasure.ennreal_mass]
        simpa [fμn, μn] using jointApproxMeasure_univ (d := d) n σ ν0 hσmass0
      have hm0 : ((Mnn : NNReal) : ENNReal) = ν0 Set.univ := by
        rw [FiniteMeasure.ennreal_mass]
        simpa [Mnn, fμn, μn] using jointApproxMeasure_univ (d := d) 0 σ ν0 hσmass0
      exact hmn.trans hm0.symm
    have hμn_nonzero : ∀ n, fμn n ≠ 0 := by
      intro n hzero
      have : (fμn n).mass = 0 := by simp [hzero]
      exact hMnn_ne (hmass_const n ▸ this)
    have h_π_tight :
        IsTightMeasureSet {x : Measure Ω | ∃ μ ∈ Set.range πn, (μ : Measure Ω) = x} := by
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε hε
      by_cases hεtop : ε = (⊤ : ENNReal)
      · refine ⟨∅, isCompact_empty, ?_⟩
        intro μ hμ
        simp [hεtop]
      · let η : ℝ := (Mnn : ℝ) * ε.toReal
        have hηpos : 0 < η := by
          dsimp [η]
          exact mul_pos hMnn_pos (ENNReal.toReal_pos (ne_of_gt hε) hεtop)
        obtain ⟨K, R, hKR⟩ := htight η hηpos
        refine ⟨((Set.Icc (-1) K).prod (Metric.closedBall (0 : Fin d → ℝ) (R + 1))),
          isCompact_Icc.prod (isCompact_closedBall (0 : Fin d → ℝ) (R + 1)), ?_⟩
        intro μ hμ
        rcases hμ with ⟨μ', hμ', rfl⟩
        rcases hμ' with ⟨n, rfl⟩
        rw [show (πn n : Measure Ω) = (((fμn n).mass)⁻¹ : NNReal) • μn n by
          rw [show πn n = (fμn n).normalize by rfl]
          simpa [fμn] using (fμn n).toMeasure_normalize_eq_of_nonzero (hμn_nonzero n)]
        rw [Measure.smul_apply]
        calc
          (((((fμn n).mass)⁻¹ : NNReal) : ENNReal) *
              μn n ((((Set.Icc (-1) K).prod (Metric.closedBall (0 : Fin d → ℝ) (R + 1)))ᶜ)))
              ≤ (((((fμn n).mass)⁻¹ : NNReal) : ENNReal) * ENNReal.ofReal η) := by
                gcongr
                exact hKR n
          _ = ε := by
                rw [hmass_const n, show ENNReal.ofReal η = (Mnn : ENNReal) * ε by
                  dsimp [η]
                  rw [ENNReal.ofReal_mul hMnn_pos.le,
                    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hεtop]]
                rw [← mul_assoc, ← ENNReal.coe_mul,
                  inv_mul_cancel₀ hMnn_ne, ENNReal.coe_one, one_mul]
    have h_compact : IsCompact (closure (Set.range πn)) :=
      isCompact_closure_of_isTightMeasureSet h_π_tight
    have h_seq : IsSeqCompact (closure (Set.range πn)) := h_compact.isSeqCompact
    have hfreq : ∃ᶠ n in atTop, πn n ∈ closure (Set.range πn) := by
      refine Filter.Eventually.frequently ?_
      exact Filter.Eventually.of_forall (fun n => subset_closure (Set.mem_range_self n))
    obtain ⟨π0, -, φ, hφmono, h_tendstoπ⟩ := h_seq.subseq_of_frequently_in hfreq
    let μ : Measure Ω := (Mnn : ENNReal) • ((π0 : ProbabilityMeasure Ω) : Measure Ω)
    haveI hμ_fin : IsFiniteMeasure μ := by
      dsimp [μ]
      exact Measure.smul_finite _ (by simp)
    have hπn_zero :
        ∀ n, ((πn n : ProbabilityMeasure Ω) : Measure Ω)
          (((Set.Iio 0).prod Set.univ) : Set Ω) = 0 := by
      intro n
      rw [show (πn n : Measure Ω) = ((((fμn n).mass)⁻¹ : NNReal) : ENNReal) • μn n by
        rw [show πn n = (fμn n).normalize by rfl]
        simpa [fμn] using (fμn n).toMeasure_normalize_eq_of_nonzero (hμn_nonzero n)]
      rw [Measure.smul_apply, hμn_supp n]
      simp
    have hπ0_zero :
        ((π0 : ProbabilityMeasure Ω) : Measure Ω) (((Set.Iio 0).prod Set.univ) : Set Ω) = 0 := by
      have hle :
          ((π0 : ProbabilityMeasure Ω) : Measure Ω) (((Set.Iio 0).prod Set.univ) : Set Ω) ≤
            Filter.atTop.liminf
              (fun n => ((πn (φ n) : ProbabilityMeasure Ω) : Measure Ω)
                ((((Set.Iio 0).prod Set.univ) : Set Ω))) := by
        simpa using
          (ProbabilityMeasure.le_liminf_measure_open_of_tendsto
            (μs_lim := h_tendstoπ)
            (G := (((Set.Iio (0 : ℝ)).prod Set.univ) : Set Ω))
            ((isOpen_Iio : IsOpen (Set.Iio (0 : ℝ))).prod isOpen_univ))
      apply le_antisymm
      · refine le_trans hle ?_
        simp [hπn_zero]
      · exact zero_le _
    have hsupp_μ : μ (((Set.Iio 0).prod Set.univ) : Set Ω) = 0 := by
      dsimp [μ]
      change ((Mnn : ENNReal) * (((π0 : ProbabilityMeasure Ω) : Measure Ω)
        (((Set.Iio 0).prod Set.univ) : Set Ω))) = 0
      rw [hπ0_zero, mul_zero]
    have hμn_eq :
        ∀ n, μn n = (Mnn : ENNReal) • (((πn n : ProbabilityMeasure Ω) : Measure Ω)) := by
      intro n
      have hfm :
          (fμn n : FiniteMeasure Ω) = (fμn n).mass • (πn n).toFiniteMeasure := by
        simpa [πn] using (fμn n).self_eq_mass_smul_normalize
      have hmeas :
          (((fμn n : FiniteMeasure Ω) : Measure Ω)) =
            ((fμn n).mass : ENNReal) • (((πn n : ProbabilityMeasure Ω) : Measure Ω)) := by
        exact congrArg (fun ρ : FiniteMeasure Ω => (ρ : Measure Ω)) hfm
      simpa [fμn, hmass_const n] using hmeas
    refine ⟨μ, hμ_fin, hsupp_μ, ?_⟩
    intro t a ht
    haveI hνt_fin : IsFiniteMeasure (ν t) := hν t ht
    have hπ_char :
        Tendsto
          (fun k => ∫ z, laplaceCharBCF (d := d) t ht a z
            ∂(((πn (φ k) : ProbabilityMeasure Ω) : Measure Ω)))
          atTop
          (nhds (∫ z, laplaceCharBCF (d := d) t ht a z
            ∂(((π0 : ProbabilityMeasure Ω) : Measure Ω)))) := by
      exact
        (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h_tendstoπ
          (laplaceCharBCF (d := d) t ht a)
    have hμ_char :
        Tendsto
          (fun k => ∫ z, laplaceCharBCF (d := d) t ht a z ∂(μn (φ k)))
          atTop
          (nhds (∫ z, laplaceCharBCF (d := d) t ht a z ∂μ)) := by
      have hscaled :
          Tendsto
            (fun k => ((Mnn : ℝ) : ℂ) *
              (∫ z, laplaceCharBCF (d := d) t ht a z
                ∂(((πn (φ k) : ProbabilityMeasure Ω) : Measure Ω))))
            atTop
            (nhds (((Mnn : ℝ) : ℂ) *
              (∫ z, laplaceCharBCF (d := d) t ht a z
                ∂(((π0 : ProbabilityMeasure Ω) : Measure Ω))))) := by
        have hcont : Continuous (fun z : ℂ => ((Mnn : ℝ) : ℂ) * z) :=
          continuous_const.mul continuous_id
        exact hcont.continuousAt.tendsto.comp hπ_char
      have hμscale :
          ∀ k,
            ∫ z, laplaceCharBCF (d := d) t ht a z ∂(μn (φ k)) =
              ((Mnn : ℝ) : ℂ) *
                (∫ z, laplaceCharBCF (d := d) t ht a z
                  ∂(((πn (φ k) : ProbabilityMeasure Ω) : Measure Ω))) := by
        intro k
        rw [hμn_eq (φ k), MeasureTheory.integral_smul_measure]
        change ((Mnn : ℝ) •
          ∫ z, laplaceCharBCF (d := d) t ht a z
            ∂(((πn (φ k) : ProbabilityMeasure Ω) : Measure Ω))) =
          ((Mnn : ℝ) : ℂ) *
            (∫ z, laplaceCharBCF (d := d) t ht a z
              ∂(((πn (φ k) : ProbabilityMeasure Ω) : Measure Ω)))
        simp
      have hμscale0 :
          ∫ z, laplaceCharBCF (d := d) t ht a z ∂μ =
            ((Mnn : ℝ) : ℂ) *
              (∫ z, laplaceCharBCF (d := d) t ht a z
                ∂(((π0 : ProbabilityMeasure Ω) : Measure Ω))) := by
        change
          ∫ z, laplaceCharBCF (d := d) t ht a z
            ∂((Mnn : ENNReal) • (((π0 : ProbabilityMeasure Ω) : Measure Ω))) =
            ((Mnn : ℝ) : ℂ) *
              (∫ z, laplaceCharBCF (d := d) t ht a z
                ∂(((π0 : ProbabilityMeasure Ω) : Measure Ω)))
        rw [MeasureTheory.integral_smul_measure]
        change ((Mnn : ℝ) •
          ∫ z, laplaceCharBCF (d := d) t ht a z
            ∂(((π0 : ProbabilityMeasure Ω) : Measure Ω))) =
          ((Mnn : ℝ) : ℂ) *
            (∫ z, laplaceCharBCF (d := d) t ht a z
              ∂(((π0 : ProbabilityMeasure Ω) : Measure Ω)))
        simp
      simpa [hμscale, hμscale0] using hscaled
    have hμ_char_raw :
        Tendsto
          (fun k =>
            ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)) ∂(μn (φ k)))
          atTop
          (nhds
            (∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)) ∂μ)) := by
      have h_eqk :
          ∀ k,
            ∫ z, laplaceCharBCF (d := d) t ht a z ∂(μn (φ k)) =
              ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)) ∂(μn (φ k)) := by
        intro k
        exact integral_laplaceCharBCF_eq (hμn_supp (φ k)) t ht a
      have h_eq0 :
          ∫ z, laplaceCharBCF (d := d) t ht a z ∂μ =
            ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)) ∂μ := by
        exact integral_laplaceCharBCF_eq hsupp_μ t ht a
      simpa [h_eqk, h_eq0] using hμ_char
    have hgrid_lim :
        Tendsto
          (fun k =>
            ∫ q, exp (I * ↑(∑ i : Fin d, gridStep (d := d) (φ k) q i * a i)) ∂(ν t))
          atTop
          (nhds (∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))) := by
      apply tendsto_integral_of_dominated_convergence (bound := fun _ => (1 : ℝ))
      · intro n
        apply Measurable.aestronglyMeasurable
        apply Measurable.cexp
        apply Measurable.mul measurable_const
        exact Complex.continuous_ofReal.measurable.comp <| by
          simpa using
            (Finset.measurable_sum Finset.univ fun i _ =>
              Measurable.mul
                (measurable_pi_apply i |>.comp (measurable_gridStep (d := d) (φ n)))
                measurable_const)
      · exact integrable_const (1 : ℝ)
      · intro n
        apply Filter.Eventually.of_forall
        intro q
        have hnorm : ‖exp (I * ↑(∑ i : Fin d, gridStep (d := d) (φ n) q i * a i))‖ = 1 := by
          simpa [mul_comm] using
            (Complex.norm_exp_ofReal_mul_I (∑ i : Fin d, gridStep (d := d) (φ n) q i * a i))
        linarith
      · apply Filter.Eventually.of_forall
        intro q
        have hcont :
            Continuous (fun q' : Fin d → ℝ => exp (I * ↑(∑ i : Fin d, q' i * a i))) := by
          apply Continuous.cexp
          apply Continuous.mul continuous_const
          exact Complex.continuous_ofReal.comp <|
            continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)
        exact hcont.continuousAt.tendsto.comp
          ((tendsto_gridStep (d := d) q).comp (StrictMono.tendsto_atTop hφmono))
    have hμn_repr' :
        ∀ k,
          ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)) ∂(μn (φ k))
            =
          ∫ q, exp (I * ↑(∑ i : Fin d, gridStep (d := d) (φ k) q i * a i)) ∂(ν t) := by
      intro k
      rw [hμn_repr (φ k) t a ht, integral_gridStep_char_eq_tsum (d := d) ν t a (φ k)]
    have hleft_lim :
        Tendsto
          (fun k =>
            ∫ z, exp (-(↑(t * z.1) : ℂ)) * exp (I * ↑(∑ i : Fin d, z.2 i * a i)) ∂(μn (φ k)))
          atTop
          (nhds (∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))) := by
      refine Tendsto.congr' ?_ hgrid_lim
      exact Filter.Eventually.of_forall (fun k => (hμn_repr' k).symm)
    exact tendsto_nhds_unique hleft_lim hμ_char_raw

/-- Product measure assembly from the formalized temporal slice analysis,
plus the two remaining external inputs above. -/
theorem product_measure_assembly {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (_hpd : IsSemigroupGroupPD d F)
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
  let slice : ∀ B : {B : Set (Fin d → ℝ) // MeasurableSet B}, TemporalSliceRep ν B.1 :=
    fun B => temporalSliceRepOf ν B.1
      (hνPD B.1 B.2)
      (spatial_slice_measure_continuous F hcont hbdd ν hν hνF hνPD B.1 B.2)
      (spatial_slice_bounded F hbdd ν hν hνF B.1)
  let σ : {B : Set (Fin d → ℝ) // MeasurableSet B} → Measure ℝ := fun B => (slice B).σ
  have hσfin : ∀ B, IsFiniteMeasure (σ B) := by
    intro B
    dsimp [σ]
    infer_instance
  have hσsupp : ∀ B, σ B (Set.Iio 0) = 0 := by
    intro B
    exact (slice B).support
  have hσlaplace : ∀ B t, 0 ≤ t → ((ν t) B.1).toReal = ∫ p, Real.exp (-(t * p)) ∂(σ B) := by
    intro B t ht
    exact (slice B).laplace t ht
  have hσiUnion : ∀ (B : ℕ → Set (Fin d → ℝ)) (hB : ∀ n, MeasurableSet (B n))
      (hdisj : Pairwise (Function.onFun Disjoint B)),
      σ ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩ =
        Measure.sum (fun n => σ ⟨B n, hB n⟩) := by
    intro B hB hdisj
    exact TemporalSliceRep.iUnion_eq hν B hB hdisj
      (fun n => slice ⟨B n, hB n⟩)
      (slice ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩)
  obtain ⟨μ, hμfin, hμsupp, hμrepr⟩ :=
    joint_measure_from_temporal_slices ν hν σ hσfin hσsupp hσlaplace hσiUnion
  refine ⟨μ, hμfin, hμsupp, ?_⟩
  intro t a ht
  exact (hνF t ht a).trans (hμrepr t a ht)

/-! ## Main theorem -/

/-! ### Laplace-Fourier Uniqueness (BCR 4.1.13, uniqueness clause) -/

/-- The t-weighted spatial measure: pushforward of `e^{-tp₁} dμ` to `ℝ^d`. -/
private noncomputable def weightedSpatialMeasure {d : ℕ}
    (μ : Measure (ℝ × (Fin d → ℝ))) (t : ℝ) : Measure (Fin d → ℝ) :=
  Measure.map Prod.snd
    (μ.withDensity (fun p => ENNReal.ofReal (Real.exp (-t * p.1))))

/-- The temporal slice measure: `η^E(A) = μ(A ×ˢ E)`. -/
private noncomputable def temporalSliceMeasure {d : ℕ}
    (μ : Measure (ℝ × (Fin d → ℝ))) (E : Set (Fin d → ℝ)) : Measure ℝ :=
  Measure.map Prod.fst (μ.restrict (Set.univ ×ˢ E))

private lemma temporalSliceMeasure_apply {d : ℕ}
    (μ : Measure (ℝ × (Fin d → ℝ))) (E : Set (Fin d → ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    temporalSliceMeasure μ E A = μ (A ×ˢ E) := by
  simp only [temporalSliceMeasure]
  rw [Measure.map_apply measurable_fst hA,
      Measure.restrict_apply (measurable_fst hA)]
  congr 1; ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
    Set.mem_univ, true_and]

private lemma temporalSliceMeasure_isFiniteMeasure {d : ℕ}
    (μ : Measure (ℝ × (Fin d → ℝ))) [IsFiniteMeasure μ]
    (E : Set (Fin d → ℝ)) :
    IsFiniteMeasure (temporalSliceMeasure μ E) where
  measure_univ_lt_top := by
    simp only [temporalSliceMeasure]
    rw [Measure.map_apply measurable_fst MeasurableSet.univ,
        Set.preimage_univ]
    exact lt_of_le_of_lt (Measure.restrict_le_self _)
      (measure_lt_top μ _)

private lemma temporalSliceMeasure_support {d : ℕ}
    (μ : Measure (ℝ × (Fin d → ℝ))) [IsFiniteMeasure μ]
    (hsupp : μ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (E : Set (Fin d → ℝ)) :
    temporalSliceMeasure μ E (Set.Iio 0) = 0 := by
  rw [temporalSliceMeasure_apply _ _ measurableSet_Iio]
  exact le_antisymm
    (le_trans
      (measure_mono (Set.prod_mono_right (Set.subset_univ E)))
      (le_of_eq hsupp))
    (zero_le _)

/-- Fourier uniqueness for the weighted spatial measures. -/
private lemma weightedSpatial_eq_of_laplaceFourier_eq {d : ℕ}
    (μ₁ μ₂ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hsupp₁ : μ₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₂ : μ₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (heq : ∀ (t : ℝ), 0 < t → ∀ (a : Fin d → ℝ),
      ∫ p : ℝ × (Fin d → ℝ),
        exp (-(↑(t * p.1) : ℂ)) *
          exp (I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ₁ =
      ∫ p : ℝ × (Fin d → ℝ),
        exp (-(↑(t * p.1) : ℂ)) *
          exp (I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ₂)
    {t : ℝ} (ht : 0 < t) :
    weightedSpatialMeasure μ₁ t = weightedSpatialMeasure μ₂ t := by
  -- Establish IsFiniteMeasure for weighted spatial measures via support bound
  have ae_nonneg : ∀ (μ : Measure (ℝ × (Fin d → ℝ))),
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 → ∀ᵐ p ∂μ, 0 ≤ p.1 := by
    intro μ hsupp; rw [ae_iff]
    have : {a : ℝ × (Fin d → ℝ) | ¬ 0 ≤ a.1} =
        (Set.Iio 0).prod Set.univ := by
      ext ⟨x, y⟩
      exact ⟨fun h => ⟨not_le.mp h, trivial⟩, fun h => not_le.mpr h.1⟩
    rw [this]; exact hsupp
  have mk_finite : ∀ (μ : Measure (ℝ × (Fin d → ℝ))) [IsFiniteMeasure μ],
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 →
      IsFiniteMeasure (weightedSpatialMeasure μ t) := by
    intro μ _ hsupp
    have : IsFiniteMeasure
        (μ.withDensity
          (fun p => ENNReal.ofReal (Real.exp (-t * p.1)))) := by
      apply isFiniteMeasure_withDensity
      apply ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
      calc ∫⁻ p, ENNReal.ofReal (Real.exp (-t * p.1)) ∂μ
          ≤ ∫⁻ _, 1 ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_nonneg μ hsupp] with p hp
            rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]; nlinarith
        _ = μ Set.univ := by simp
    exact Measure.isFiniteMeasure_map _ _
  haveI := mk_finite μ₁ hsupp₁
  haveI := mk_finite μ₂ hsupp₂
  -- Apply Fourier uniqueness
  apply fourier_uniqueness_finite_measure
  intro a
  -- Convert Fourier integrals over wsm to integrals over μ
  have fourier_conv : ∀ (μ : Measure (ℝ × (Fin d → ℝ))) [IsFiniteMeasure μ],
      ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i))
        ∂(weightedSpatialMeasure μ t) =
      ∫ p : ℝ × (Fin d → ℝ),
        exp (-(↑(t * p.1) : ℂ)) *
          exp (I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ := by
    intro μ _
    have lhs := integral_map (f := fun q : Fin d → ℝ =>
        exp (I * ↑(∑ i : Fin d, q i * a i)))
      (μ := μ.withDensity
        (fun p => ENNReal.ofReal (Real.exp (-t * p.1))))
      measurable_snd.aemeasurable
      ((Complex.continuous_exp.comp
        (Continuous.mul continuous_const
          (continuous_ofReal.comp
            (continuous_finset_sum _ fun i _ =>
              (continuous_apply i).mul
                continuous_const)))).aestronglyMeasurable)
    simp only [weightedSpatialMeasure] at lhs ⊢
    rw [lhs, integral_withDensity_eq_integral_toReal_smul₀
      (by fun_prop : AEMeasurable
        (fun p : ℝ × (Fin d → ℝ) =>
          ENNReal.ofReal (Real.exp (-t * p.1))) μ)
      (by filter_upwards with p; exact ENNReal.ofReal_lt_top)]
    congr 1; ext p
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    change (↑(Real.exp (-t * p.1)) : ℂ) * _ = _
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [fourier_conv μ₁, fourier_conv μ₂]
  exact heq t ht a

/-- Laplace equality for temporal slices follows from weighted spatial equality. -/
private lemma temporalSlice_laplace_eq {d : ℕ}
    (μ₁ μ₂ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (hsupp₁ : μ₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hsupp₂ : μ₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (hws : ∀ t, 0 < t →
      weightedSpatialMeasure μ₁ t = weightedSpatialMeasure μ₂ t)
    (E : Set (Fin d → ℝ)) (hE : MeasurableSet E) :
    ∀ t, 0 ≤ t →
      ∫ p : ℝ, Real.exp (-(t * p)) ∂(temporalSliceMeasure μ₁ E) =
      ∫ p : ℝ, Real.exp (-(t * p)) ∂(temporalSliceMeasure μ₂ E) := by
  intro t ht
  -- Conversion: temporal slice Laplace integral = (wsm μ t)(E).toReal
  have tsm_conv : ∀ (μ : Measure (ℝ × (Fin d → ℝ))) [IsFiniteMeasure μ]
      (s : ℝ),
      ∫ p, Real.exp (-(s * p)) ∂(temporalSliceMeasure μ E) =
      (weightedSpatialMeasure μ s E).toReal := by
    intro μ _ s
    have lhs := integral_map
      (f := fun p : ℝ => Real.exp (-(s * p)))
      (μ := μ.restrict (Set.univ ×ˢ E))
      measurable_fst.aemeasurable
      ((Real.continuous_exp.comp
        ((continuous_const.mul continuous_id').neg)).aestronglyMeasurable)
    simp only [temporalSliceMeasure, weightedSpatialMeasure] at lhs ⊢
    rw [lhs, Measure.map_apply measurable_snd hE,
        withDensity_apply _ (measurable_snd hE)]
    have hset : (Prod.snd ⁻¹' E : Set (ℝ × (Fin d → ℝ))) =
        Set.univ ×ˢ E := by
      ext p; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [hset, ← integral_toReal
      ((by fun_prop : Measurable (fun p : ℝ × (Fin d → ℝ) =>
        ENNReal.ofReal (Real.exp (-s * p.1)))).aemeasurable.restrict)
      (by filter_upwards with p; exact ENNReal.ofReal_lt_top)]
    congr 1; ext p
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]; ring
  -- Case t > 0: use wsm equality
  have hpos_eq : ∀ s, 0 < s →
      ∫ p, Real.exp (-(s * p)) ∂(temporalSliceMeasure μ₁ E) =
      ∫ p, Real.exp (-(s * p)) ∂(temporalSliceMeasure μ₂ E) := by
    intro s hs
    rw [tsm_conv μ₁ s, tsm_conv μ₂ s,
        congrFun (congrArg DFunLike.coe (hws s hs)) E]
  rcases eq_or_lt_of_le ht with rfl | hpos
  · -- Case t = 0: dominated convergence with tₙ = 1/(n+1)
    set ν₁ := temporalSliceMeasure μ₁ E
    set ν₂ := temporalSliceMeasure μ₂ E
    haveI := temporalSliceMeasure_isFiniteMeasure μ₁ E
    haveI := temporalSliceMeasure_isFiniteMeasure μ₂ E
    have hs₁ := temporalSliceMeasure_support μ₁ hsupp₁ E
    have hs₂ := temporalSliceMeasure_support μ₂ hsupp₂ E
    set seq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have hseq_pos : ∀ n, 0 < seq n := fun n => by positivity
    have hF_meas : ∀ (n : ℕ) (ν : Measure ℝ),
        AEStronglyMeasurable
          (fun p => Real.exp (-(seq n * p))) ν :=
      fun n _ => (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id').neg)).aestronglyMeasurable
    have hbound : ∀ (ν : Measure ℝ), ν (Set.Iio 0) = 0 →
        ∀ n, ∀ᵐ p ∂ν, ‖Real.exp (-(seq n * p))‖ ≤ 1 := by
      intro ν hνs n
      have hae : ∀ᵐ p ∂ν, 0 ≤ p := by
        rw [ae_iff]; simpa [not_le] using hνs
      filter_upwards [hae] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
          Real.exp_le_one_iff]
      exact neg_nonpos_of_nonneg
        (mul_nonneg (le_of_lt (hseq_pos n)) hp)
    have hlim : ∀ p : ℝ, Tendsto
        (fun n => Real.exp (-(seq n * p))) atTop
        (nhds (Real.exp (-(0 * p)))) :=
      fun p => (Real.continuous_exp.tendsto _).comp
        (Tendsto.neg ((tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right atTop 1
            tendsto_natCast_atTop_atTop)).mul_const p))
    exact tendsto_nhds_unique
      (tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun n => hF_meas n ν₁) (integrable_const 1)
        (hbound ν₁ hs₁) (ae_of_all _ hlim))
      ((tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun n => hF_meas n ν₂) (integrable_const 1)
        (hbound ν₂ hs₂) (ae_of_all _ hlim)).congr
        (fun n => (hpos_eq (seq n) (hseq_pos n)).symm))
  · exact hpos_eq t hpos

/-- **Laplace-Fourier uniqueness** on `[0,∞) × ℝ^d`.

Finite positive measures supported on `[0,∞) × ℝ^d` are determined by
their joint Laplace-Fourier transform on `t > 0`. This is the uniqueness
clause of BCR Theorem 4.1.13.

The proof uses `ext_prod` (Mathlib): two finite measures agreeing on
all measurable rectangles are equal. Rectangle equality follows from
`laplace_measure_unique` (temporal) and
`fourier_uniqueness_finite_measure` (spatial). -/
theorem laplaceFourier_unique {d : ℕ}
    (μ₁ μ₂ : Measure (ℝ × (Fin d → ℝ)))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h₁ : μ₁ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (h₂ : μ₂ (Set.prod (Set.Iio 0) Set.univ) = 0)
    (heq : ∀ (t : ℝ), 0 < t → ∀ (a : Fin d → ℝ),
      ∫ p : ℝ × (Fin d → ℝ),
        Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ₁ =
      ∫ p : ℝ × (Fin d → ℝ),
        Complex.exp (-(↑(t * p.1) : ℂ)) *
          Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ₂) :
    μ₁ = μ₂ := by
  -- Step 1: Weighted spatial measures agree for all t > 0
  have hws : ∀ t, 0 < t →
      weightedSpatialMeasure μ₁ t = weightedSpatialMeasure μ₂ t :=
    fun t ht => weightedSpatial_eq_of_laplaceFourier_eq μ₁ μ₂ h₁ h₂ heq ht
  -- Step 2: For each measurable E, temporal slice measures agree
  -- (Laplace transforms agree → laplace_measure_unique)
  have hslice : ∀ E, MeasurableSet E →
      temporalSliceMeasure μ₁ E = temporalSliceMeasure μ₂ E := by
    intro E hE
    haveI := temporalSliceMeasure_isFiniteMeasure μ₁ E
    haveI := temporalSliceMeasure_isFiniteMeasure μ₂ E
    exact laplace_measure_unique
      (temporalSliceMeasure μ₁ E) (temporalSliceMeasure μ₂ E)
      (temporalSliceMeasure_support μ₁ h₁ E)
      (temporalSliceMeasure_support μ₂ h₂ E)
      (temporalSlice_laplace_eq μ₁ μ₂ h₁ h₂ hws E hE)
  -- Step 3: Measures agree on all rectangles → ext_prod
  exact Measure.ext_prod (fun hS hT => by
    have := hslice _ hT
    rw [← temporalSliceMeasure_apply μ₁ _ hS,
        ← temporalSliceMeasure_apply μ₂ _ hS, this])

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
