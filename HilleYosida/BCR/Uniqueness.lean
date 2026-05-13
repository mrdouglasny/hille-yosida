/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.
-/

import HilleYosida.BCR.Common
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.ContinuousMap.Weierstrass

/-! # BCR Theorem 4.1.13 — uniqueness

Proves `laplaceFourier_unique`: finite measures on `[0,∞) × ℝ^d` whose
Fourier-Laplace transforms agree on `[0,∞) × ℝ^d` coincide.

The argument runs in two stages:
* **Stage 1** — Fourier uniqueness on the `t`-weighted spatial measures
  (`weightedSpatial_eq_of_laplaceFourier_eq`).
* **Stage 2** — Laplace uniqueness on each temporal slice
  (`temporalSlice_laplace_eq`), invoking `laplace_measure_unique` from
  `BCR_Common`.

Combined, these give `Measure.ext_prod` on the rectangle algebra. -/

noncomputable section

open MeasureTheory Complex Set Filter Finset
open scoped Polynomial

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

end
