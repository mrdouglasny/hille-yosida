/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bernstein's Theorem — Chafai identity and Prokhorov extraction

`cm_rescaled_isFiniteMeasure`, `chafai_kernel_density_eq`,
`chafai_repeated_ibp`, `chafai_identity`, `finite_measure_subseq_limit`,
Prokhorov extraction, `prokhorov_limit_identification`.

Split from `Bernstein.lean`.
-/

import HilleYosida.BernsteinMeasures
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

noncomputable section

open MeasureTheory Set intervalIntegral Filter

/-! ### Prokhorov extraction + Laplace representation -/

/-- The rescaled measure `cm_rescaled f n` is a finite measure when the
underlying `cm_measure f n` is finite. -/
lemma cm_rescaled_isFiniteMeasure (f : ℝ → ℝ) (n : ℕ)
    [IsFiniteMeasure (cm_measure f n)] :
    IsFiniteMeasure (cm_rescaled f n) where
  measure_univ_lt_top := by
    unfold cm_rescaled
    rw [Measure.map_apply (cm_rescaling_measurable n) MeasurableSet.univ, Set.preimage_univ]
    exact IsFiniteMeasure.measure_univ_lt_top

/-! **Chafaï identity**: For a CM function `f` with `f(t) → L` and `n ≥ 2, x ≥ 0`:

  `f(x) - L = ∫ φ_n(x,p) dσ̃_n(p)`

where `φ_n` is `bernstein_kernel` and `σ̃_n = cm_rescaled f n`.

**Proof sketch** (Chafaï 2013): The Taylor integral remainder on `[x, T]` gives
  `f(x) - f(T) + B_n(T) = ∫_x^T ρ_n(t) dt`
where `B_n(T) ≤ 0` by the CM sign condition.
The change of variables `p = (n-1)/t` transforms the RHS to
  `∫ φ_n(x,p) dσ̃_n|_{[(n-1)/T,∞)}(p)`.
As `T → ∞`: `f(T) → L`, `B_n(T) → 0` (boundary decay for CM functions:
`T^k f^{(k)}(T) → 0` from integrability + monotonicity of `(-1)^k f^{(k)}`),
and the integration domain fills `[0, ∞)`.

The change of variables is proved in `chafai_kernel_density_eq` (sorry-free).
The boundary decay integral is in `chafai_repeated_ibp` (sorry).

The kernel-density simplification needs extra heartbeats for field_simp. -/
set_option maxHeartbeats 3200000 in
-- Kernel-density simplification requires extra heartbeats for field_simp reasoning.
private lemma chafai_kernel_density_eq (f : ℝ → ℝ) (_hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in Set.Ioi 0, bernstein_kernel n x (((n : ℝ) - 1) / t) *
      cm_density f n t =
    ∫ t in Set.Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) * iteratedDerivWithin n f (Set.Ici 0) t := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : ¬(n ≤ 1) := by omega
  have hne : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsubset : Set.Ioi x ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi hx
  have hvanish : ∀ t ∈ Set.Ioi 0 \ Set.Ioi x,
      bernstein_kernel n x (((n : ℝ) - 1) / t) * cm_density f n t = 0 := by
    intro t ht
    simp only [Set.mem_diff, Set.mem_Ioi, not_lt] at ht
    simp only [bernstein_kernel, hn1, ite_false]
    have hcast : (↑(n - 1) : ℝ) = ↑n - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
    have : x * (((n : ℝ) - 1) / t) / ↑(n - 1) = x / t := by
      rw [hcast]; field_simp [hne, ne_of_gt ht.1]
    rw [this, max_eq_right (by rw [sub_nonpos, le_div_iff₀ ht.1]; linarith)]
    rw [zero_pow (by omega : n - 1 ≠ 0), zero_mul]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Ioi hsubset hvanish]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht; simp only [Set.mem_Ioi] at ht
  have ht_pos : 0 < t := lt_of_le_of_lt hx ht
  have hcast : (↑(n - 1) : ℝ) = ↑n - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  simp only [bernstein_kernel, hn1, ite_false]
  have hrw : x * (((n : ℝ) - 1) / t) / ↑(n - 1) = x / t := by
    rw [hcast]; field_simp [hne, ne_of_gt ht_pos]
  rw [hrw, max_eq_left (by rw [sub_nonneg, div_le_one₀ ht_pos]; linarith)]
  simp only [cm_density, hn0, ite_false]
  have key : (1 - x / t) ^ (n - 1) * t ^ (n - 1) = (t - x) ^ (n - 1) := by
    rw [← mul_pow]; congr 1; field_simp [ne_of_gt ht_pos]
  calc (1 - x / t) ^ (n - 1) * ((-1 : ℝ) ^ n / ↑(n - 1).factorial *
      t ^ (n - 1) * iteratedDerivWithin n f (Set.Ici 0) t)
      = (-1 : ℝ) ^ n / ↑(n - 1).factorial *
        ((1 - x / t) ^ (n - 1) * t ^ (n - 1)) *
        iteratedDerivWithin n f (Set.Ici 0) t := by ring
    _ = _ := by rw [key]

/-- IBP on `[x, T]`: integrating the `(k+1)`-th order Taylor kernel by parts gives
a boundary term plus the `k`-th order kernel (with a sign flip). -/
private lemma ibp_finite_interval (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x T : ℝ) (hx : 0 ≤ x) (hxT : x < T) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Set.Ici 0) t =
    (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Set.Ici 0) T -
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Set.Ici 0) t := by
  set c := (-1 : ℝ) ^ (k + 1) / ↑k.factorial
  set g := iteratedDerivWithin k f (Set.Ici 0)
  set g' := iteratedDerivWithin (k + 1) f (Set.Ici 0)
  set u := fun t : ℝ => c * (t - x) ^ k
  set u' := fun t : ℝ => c * (↑k * (t - x) ^ (k - 1))
  have hu'_eq : ∀ t, u' t =
      (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) := by
    intro t; simp only [u', c]
    have : k.factorial = k * (k - 1).factorial := by
      cases k with | zero => contradiction | succ n => simp [Nat.factorial_succ]
    rw [this]; push_cast; field_simp
  have hu_cont : ContinuousOn u (Set.uIcc x T) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow _)
  have hg_cont : ContinuousOn g (Set.uIcc x T) := by
    rw [Set.uIcc_of_le (le_of_lt hxT)]
    exact (hcm.1.continuousOn_iteratedDerivWithin (nat_le_coe_top _) (uniqueDiffOn_Ici 0)).mono
      (Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hx))
  have hu_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt u (u' t) (Ioi t) t := by
    intro t _; apply HasDerivAt.hasDerivWithinAt
    change HasDerivAt (fun t => c * (t - x) ^ k) (c * (↑k * (t - x) ^ (k - 1))) t
    convert ((hasDerivAt_pow k (t - x)).comp t
      ((hasDerivAt_id t).sub_const x)).const_mul c using 1; ring
  have hg_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt g (g' t) (Ioi t) t := by
    intro t ht
    rw [min_eq_left (le_of_lt hxT), max_eq_right (le_of_lt hxT)] at ht
    have hmem : Set.Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds (by linarith [ht.1])
    apply HasDerivAt.hasDerivWithinAt
    convert (hcm.1.differentiableOn_iteratedDerivWithin
      (nat_lt_coe_top _)
      (uniqueDiffOn_Ici 0)).hasDerivAt hmem using 1
    simp only [g', iteratedDerivWithin_succ, derivWithin_of_mem_nhds hmem]
  have hu'_int : IntervalIntegrable u' volume x T :=
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _))).intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume x T := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le (le_of_lt hxT)]
    exact (hcm.1.continuousOn_iteratedDerivWithin (nat_le_coe_top _) (uniqueDiffOn_Ici 0)).mono
      (Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hx))
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu_cont hg_cont hu_deriv hg_deriv hu'_int hg'_int
  have hu0 : u x = 0 := by simp [u, sub_self, zero_pow hk]
  rw [hu0, zero_mul, sub_zero] at hibp
  have h1 : ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
        iteratedDerivWithin (k + 1) f (Set.Ici 0) t =
      ∫ t in x..T, u t * g' t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by ring)
  have h2 : ∫ t in x..T, u' t * g t =
      ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Set.Ici 0) t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by
      rw [hu'_eq])
  linarith

/-- Tail set integral of an integrable function on `(a, ∞)` tends to 0. -/
private lemma tail_setIntegral_tendsto_zero {g : ℝ → ℝ} {a : ℝ}
    (hg : IntegrableOn g (Ioi a)) :
    Tendsto (fun T => ∫ t in Ioi T, g t) atTop (nhds 0) := by
  set I := ∫ t in Ioi a, g t
  have h_total : Tendsto (fun T => ∫ t in a..T, g t) atTop (nhds I) :=
    (intervalIntegral_tendsto_integral_Ioi a hg tendsto_id).congr fun _ => by simp [id]
  have hsub : Tendsto (fun T => I - ∫ t in a..T, g t) atTop (nhds 0) := by
    convert tendsto_const_nhds.sub h_total using 1; simp
  apply hsub.congr'
  filter_upwards [eventually_gt_atTop a] with T hT
  symm
  have hdisj : Disjoint (Ioc a T) (Ioi T) := by
    rw [disjoint_left]; intro y hy1 hy2; simp at hy1 hy2; linarith
  have hunion : Ioc a T ∪ Ioi T = Ioi a := by
    ext y; simp only [mem_union, mem_Ioc, mem_Ioi]; constructor
    · rintro (⟨hy, _⟩ | hy) <;> linarith
    · intro hy; by_cases hyT : y ≤ T
      · left; exact ⟨hy, hyT⟩
      · right; linarith
  have hd := setIntegral_union hdisj measurableSet_Ioi
    (hg.mono_set Ioc_subset_Ioi_self) (hg.mono_set (Ioi_subset_Ioi (le_of_lt hT)))
  rw [hunion] at hd; rw [intervalIntegral.integral_of_le (le_of_lt hT)]; linarith

/- Boundary decay: `(-1)^{k+1}/k! (T-x)^k D^k f(T) → 0` as `T → ∞` for CM functions.
This follows from the integrability of the k-th CM density on `(0, ∞)`. -/
set_option maxHeartbeats 6400000 in
-- Boundary-term squeeze uses repeated interval/set-integral comparisons.
-- Needs extra heartbeats for nested integrable/antitone/tail reasoning chains.
private lemma boundary_term_decay (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto (fun T => (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Set.Ici 0) T) Filter.atTop (nhds 0) := by
  set h := fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T
  have hkey : Tendsto (fun T => (T - x) ^ k * h T) atTop (nhds 0) := by
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T := by
      intro T hT
      simpa [h] using hcm.2 k T hT
    have h_antitone : AntitoneOn h (Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · simpa [h] using
          (hcm.1.continuousOn_iteratedDerivWithin (nat_le_coe_top _) (uniqueDiffOn_Ici 0)).const_mul
            ((-1 : ℝ) ^ k)
      · rw [interior_Ici]
        intro T hT
        have hdiff :
            DifferentiableAt ℝ (iteratedDerivWithin k f (Ici 0)) T :=
          (hcm.1.differentiableOn_iteratedDerivWithin (nat_lt_coe_top _)
            (uniqueDiffOn_Ici 0)) T (Set.mem_Ici.mpr (le_of_lt hT))
            |>.differentiableAt (Ici_mem_nhds hT)
        exact (hdiff.const_mul ((-1 : ℝ) ^ k)).differentiableWithinAt
      · rw [interior_Ici]
        intro T hT
        have hderiv :
            deriv h T = (-1 : ℝ) ^ k * iteratedDerivWithin (k + 1) f (Ici 0) T := by
          simp only [h]
          rw [deriv_const_mul_field]
          rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hT), ← iteratedDerivWithin_succ]
        rw [hderiv]
        have hsign : 0 ≤ (-1 : ℝ) ^ (k + 1) * iteratedDerivWithin (k + 1) f (Ici 0) T :=
          hcm.2 (k + 1) T (le_of_lt hT)
        have : 0 ≤ -(((-1 : ℝ) ^ k) * iteratedDerivWithin (k + 1) f (Ici 0) T) := by
          simpa [pow_succ, mul_assoc] using hsign
        linarith
    have hcont_density : ContinuousOn (cm_density f k) (Ici 0) := by
      unfold cm_density
      simp only [hk, ↓reduceIte]
      exact ((continuousOn_const.mul
        ((continuousOn_pow _).mono fun _ _ => trivial)).mul
        (hcm.1.continuousOn_iteratedDerivWithin (nat_le_coe_top _) (uniqueDiffOn_Ici 0)))
    have hint_density : IntegrableOn (cm_density f k) (Set.Ioi 0) := by
      by_cases hk_eq : k = 1
      · subst hk_eq
        convert hcm.neg_deriv_integrableOn hL using 1
        ext t
        simp [cm_density, iteratedDerivWithin_one]
      · have hk2 : 2 ≤ k := by omega
        have hmeas_density :
            AEStronglyMeasurable (cm_density f k) (volume.restrict (Set.Ioi 0)) :=
          (hcont_density.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
        have hnonneg_density : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] cm_density f k :=
          (ae_restrict_mem measurableSet_Ioi).mono fun t ht => cm_density_nonneg hcm k t ht
        refine ⟨hmeas_density, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal hnonneg_density]
        obtain ⟨_, hmass⟩ := cm_measure_finite_mass f hcm k hk2 L hL
        have hmass' := hmass
        unfold cm_measure at hmass'
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass'
        exact lt_of_le_of_lt hmass' ENNReal.ofReal_lt_top
    have htail :
        Tendsto (fun S : ℝ => ∫ t in Set.Ioi S, cm_density f k t) atTop (nhds 0) :=
      tail_setIntegral_tendsto_zero hint_density
    have htail_half :
        Tendsto (fun T : ℝ => ∫ t in Set.Ioi (T / 2), cm_density f k t) atTop (nhds 0) := by
      have hhalf_map : Tendsto (fun T : ℝ => (1 / 2 : ℝ) * T) atTop atTop :=
        (Filter.tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 1 / 2 by positivity)).2 tendsto_id
      simpa [div_eq_mul_inv, mul_comm] using htail.comp hhalf_map
    have hupper :
        ∀ᶠ T in atTop,
          (T - x) ^ k * h T ≤
            ((2 : ℝ) ^ k * ↑((k - 1).factorial)) *
              ∫ t in Set.Ioi (T / 2), cm_density f k t := by
      filter_upwards [eventually_gt_atTop (max (2 * x) 2)] with T hT
      have hT2 : (2 : ℝ) < T := lt_of_le_of_lt (le_max_right (2 * x) 2) hT
      have hTpos : 0 < T := by linarith
      have hxT : x < T := by
        have h2xT : 2 * x < T := lt_of_le_of_lt (le_max_left (2 * x) 2) hT
        linarith
      have hTx_nonneg : 0 ≤ T - x := sub_nonneg.mpr hxT.le
      have hT_nonneg : 0 ≤ T := le_of_lt hTpos
      have hhalf_nonneg : 0 ≤ T / 2 := by positivity
      have hhT_nonneg : 0 ≤ h T := h_nonneg T hT_nonneg
      have h_interval_le :
          ∫ t in T / 2..T, cm_density f k t ≤ ∫ t in Set.Ioi (T / 2), cm_density f k t := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        apply setIntegral_mono_set (hint_density.mono_set (Set.Ioi_subset_Ioi hhalf_nonneg))
        · exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
            cm_density_nonneg hcm k t (lt_of_le_of_lt hhalf_nonneg ht)
        · exact ae_of_all _ fun t ht => Ioc_subset_Ioi_self ht
      have h_density_eq :
          ∀ t, cm_density f k t =
            (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t := by
        intro t
        simp only [cm_density, hk, ↓reduceIte, h]
        field_simp
      have h_const_le :
          (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T ≤
            ∫ t in T / 2..T, cm_density f k t := by
        have hmono :
            ∀ᵐ t ∂(volume.restrict (Set.Icc (T / 2) T)),
              (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T ≤ cm_density f k t := by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          have ht_nonneg : 0 ≤ t := le_trans hhalf_nonneg ht.1
          have ht_pos : 0 < t := lt_of_lt_of_le (by positivity : 0 < T / 2) ht.1
          have hpow : (T / 2) ^ (k - 1) ≤ t ^ (k - 1) := by
            exact pow_le_pow_left₀ hhalf_nonneg ht.1 _
          have hh_le : h T ≤ h t := by
            exact h_antitone ht_nonneg hT_nonneg ht.2
          have hmul :
              (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T ≤
                (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t := by
            have hcoeff_nonneg : 0 ≤ (1 / ↑((k - 1).factorial) : ℝ) := by positivity
            have hright_nonneg : 0 ≤ (1 / ↑((k - 1).factorial)) * t ^ (k - 1) := by
              exact mul_nonneg hcoeff_nonneg (pow_nonneg ht_nonneg _)
            calc
              (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T
                  ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h T := by
                    simpa [mul_assoc] using
                      mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hpow hcoeff_nonneg)
                        hhT_nonneg
              _ ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h t := by
                    exact mul_le_mul_of_nonneg_left hh_le hright_nonneg
          simpa [h_density_eq t] using hmul
        have hconst_int :
            IntervalIntegrable (fun _ : ℝ =>
              (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) volume (T / 2) T :=
          intervalIntegral.intervalIntegrable_const
        have hIcc_subset : Set.Icc (T / 2) T ⊆ Set.Ici 0 := by
          intro t ht
          exact le_trans hhalf_nonneg ht.1
        have hdens_int : IntervalIntegrable (cm_density f k) volume (T / 2) T :=
          (hcont_density.mono hIcc_subset).intervalIntegrable_of_Icc (by linarith)
        have hmono_int :=
          intervalIntegral.integral_mono_ae_restrict (μ := volume) (a := T / 2) (b := T)
            (hab := by linarith) hconst_int hdens_int hmono
        rw [intervalIntegral.integral_const] at hmono_int
        have hhalf_eq : (T - T / 2) = T / 2 := by ring
        rw [hhalf_eq] at hmono_int
        rw [smul_eq_mul] at hmono_int
        have hconst_eq :
            T / 2 * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) =
              (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T := by
          have hk_succ : k = (k - 1) + 1 := by omega
          rw [hk_succ]
          ring_nf
          have hnat : 1 + (k - 1) - 1 = k - 1 := by omega
          simp [hnat]
        rw [hconst_eq] at hmono_int
        exact hmono_int
      have hhalf_le :
          (T / 2) ^ k * h T ≤ ↑((k - 1).factorial) * ∫ t in Set.Ioi (T / 2), cm_density f k t := by
        have hfact_pos : (0 : ℝ) < ↑((k - 1).factorial) := by
          exact Nat.cast_pos.mpr (Nat.factorial_pos _)
        have haux := le_trans h_const_le h_interval_le
        have hmul := mul_le_mul_of_nonneg_left haux hfact_pos.le
        have hleft_eq :
            ↑((k - 1).factorial) *
                ((1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T) =
              (T / 2) ^ k * h T := by
          field_simp [hfact_pos.ne']
        rw [hleft_eq] at hmul
        exact hmul
      have hpow_le : (T - x) ^ k ≤ T ^ k := by
        exact pow_le_pow_left₀ hTx_nonneg (by linarith) _
      have hTk_eq : T ^ k * h T = (2 : ℝ) ^ k * ((T / 2) ^ k * h T) := by
        calc
          T ^ k * h T = ((2 : ℝ) * (T / 2)) ^ k * h T := by congr 1; field_simp
          _ = (2 : ℝ) ^ k * ((T / 2) ^ k * h T) := by rw [mul_pow]; ring
      calc
        (T - x) ^ k * h T ≤ T ^ k * h T := by
          gcongr
        _ = (2 : ℝ) ^ k * ((T / 2) ^ k * h T) := hTk_eq
        _ ≤ (2 : ℝ) ^ k * (↑((k - 1).factorial) * ∫ t in Set.Ioi (T / 2), cm_density f k t) := by
          gcongr
        _ = ((2 : ℝ) ^ k * ↑((k - 1).factorial)) *
              ∫ t in Set.Ioi (T / 2), cm_density f k t := by ring
    have hnonneg_event : ∀ᶠ T in atTop, 0 ≤ (T - x) ^ k * h T := by
      filter_upwards [eventually_gt_atTop (max x 0)] with T hT
      have hT0 : 0 < T := lt_of_le_of_lt (le_max_right x 0) hT
      have hxT : x < T := lt_of_le_of_lt (le_max_left x 0) hT
      exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hxT.le) _) (h_nonneg T hT0.le)
    have hupper_tendsto :
        Tendsto (fun T : ℝ =>
          ((2 : ℝ) ^ k * ↑((k - 1).factorial)) *
            ∫ t in Set.Ioi (T / 2), cm_density f k t) atTop (nhds 0) := by
      simpa [mul_zero] using htail_half.const_mul (((2 : ℝ) ^ k) * ↑((k - 1).factorial))
    exact squeeze_zero' hnonneg_event hupper hupper_tendsto
  have heq : ∀ T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Ici 0) T =
      -(1 / ↑k.factorial) * ((T - x) ^ k * h T) := by
    intro T; simp only [h, pow_succ]; ring
  simp_rw [heq]
  rw [show (0 : ℝ) = -(1 / ↑k.factorial) * 0 from by ring]
  exact hkey.const_mul _

set_option maxHeartbeats 12800000 in
-- domination by cm_density + integrableOn_Ioi_of_intervalIntegral_norm_bounded
/-- Integrability of the k-th Taylor kernel `(-1)^k/(k-1)! (t-x)^{k-1} D^k f` on `(x, ∞)`.
Follows from the integrability of `cm_density f k` on `(0, ∞)` and the shift `t ↦ t - x`. -/
private lemma ibp_kernel_integrableOn (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    IntegrableOn (fun t => (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Set.Ici 0) t) (Set.Ioi x) := by
  -- Dominated by cm_density f k on Ioi x ⊆ Ioi 0:
  -- (t-x)^{k-1} ≤ t^{k-1} for t ≥ x ≥ 0, cm_density integrable.
  have hk0 : k ≠ 0 := by omega
  have hcont_density : ContinuousOn (cm_density f k) (Ici 0) := by
    unfold cm_density; simp only [hk0, ↓reduceIte]
    exact ((continuousOn_const.mul
      ((continuousOn_pow _).mono fun _ _ => trivial)).mul
      (hcm.1.continuousOn_iteratedDerivWithin (nat_le_coe_top _) (uniqueDiffOn_Ici 0)))
  -- ∫₀ᵀ cm_density f j ≤ f(0) - f(T) for j ≥ 1
  have density_le : ∀ j, 1 ≤ j → ∀ T, 0 < T →
      ∫ t in (0 : ℝ)..T, cm_density f j t ≤ f 0 - f T := by
    intro j hj; induction j with
    | zero => omega
    | succ p ih =>
      intro T hT; by_cases hp : p = 0
      · subst hp
        rw [intervalIntegral.integral_congr_ae
          (Filter.Eventually.of_forall fun t _ => cm_density_one t),
          ← hcm.integral_neg_deriv_Ici T hT, hcm.integral_mass T hT]
      · calc ∫ t in (0 : ℝ)..T, cm_density f (p + 1) t
            ≤ ∫ t in (0 : ℝ)..T, cm_density f p t := by
              simpa using cm_density_ibp_step f hcm (p + 1) (by omega) T hT
          _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp) T hT
  -- f(T) ≥ L
  have hfT_ge_L : ∀ T, 0 < T → L ≤ f T := by
    intro T hT
    set g₀ := fun t : ℝ => f (max t 0)
    have hg_anti : Antitone g₀ := fun a b hab =>
      (antitoneOn_of_deriv_nonpos (convex_Ici 0) hcm.1.continuousOn
        ((hcm.1.differentiableOn coe_top_ne_zero).mono interior_subset)
        (fun y hy => by
          rw [interior_Ici] at hy
          have h1 := hcm.deriv_nonpos y (le_of_lt hy)
          rwa [iteratedDerivWithin_one,
            derivWithin_of_mem_nhds (Ici_mem_nhds hy)] at h1))
        (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
        (max_le_max_right 0 hab)
    have := hg_anti.le_of_tendsto
      (hL.congr' (Filter.eventually_atTop.mpr
        ⟨0, fun t ht => by simp [g₀, max_eq_left ht]⟩)) T
    simp only [g₀, max_eq_left (le_of_lt hT)] at this; exact this
  -- cm_density integrable on (0, ∞)
  have hint_density : IntegrableOn (cm_density f k) (Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
      (l := Filter.atTop) (b := id)
    · intro T
      exact (hcont_density.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
        |>.mono_set Ioc_subset_Icc_self
    · exact Filter.tendsto_id
    · filter_upwards [Filter.eventually_gt_atTop 0] with T hT; simp only [id]
      calc ∫ t in (0 : ℝ)..T, ‖cm_density f k t‖
          = ∫ t in (0 : ℝ)..T, cm_density f k t := by
            apply intervalIntegral.integral_congr_ae; apply ae_of_all
            intro t ht; rw [uIoc_of_le (le_of_lt hT)] at ht
            rw [Real.norm_eq_abs, abs_of_nonneg (cm_density_nonneg hcm k t ht.1)]
        _ ≤ f 0 - L := by linarith [density_le k hk T hT, hfT_ge_L T hT]
  -- Domination: |integrand| ≤ cm_density f k on Ioi x ⊆ Ioi 0
  apply Integrable.mono' (hint_density.mono_set (Ioi_subset_Ioi hx))
  · apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi)
    exact ((continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _)).mul
      ((hcm.1.continuousOn_iteratedDerivWithin (nat_le_coe_top _) (uniqueDiffOn_Ici 0)).mono
        (fun t ht => mem_Ici.mpr (le_of_lt (lt_of_le_of_lt hx ht)))))
  · rw [ae_restrict_iff' measurableSet_Ioi]; apply ae_of_all; intro t ht
    simp only [Ioi, mem_setOf_eq] at ht
    have ht0 : 0 < t := lt_of_le_of_lt hx ht
    have htx : 0 ≤ t - x := by linarith
    have htx_le : t - x ≤ t := by linarith
    simp only [cm_density, hk0, ↓reduceIte]
    have hcm_sign : 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t :=
      hcm.2 k t (le_of_lt ht0)
    have hfact : (0 : ℝ) < ↑(k - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hval_nn : 0 ≤ (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t := by
      calc (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
            iteratedDerivWithin k f (Ici 0) t
          = (t - x) ^ (k - 1) / ↑(k - 1).factorial *
            ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
        _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg htx _) hfact.le) hcm_sign
    rw [Real.norm_eq_abs, abs_of_nonneg hval_nn]
    calc (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t
        = (1 / ↑(k - 1).factorial) * (t - x) ^ (k - 1) *
          ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
      _ ≤ (1 / ↑(k - 1).factorial) * t ^ (k - 1) *
          ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htx htx_le _) (by positivity))
            hcm_sign
      _ = (-1 : ℝ) ^ k / ↑(k - 1).factorial * t ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t := by field_simp

set_option maxHeartbeats 6400000 in
-- Repeated IBP induction with boundary decay requires many integrable/limit steps.
private lemma chafai_repeated_ibp (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    ∫ t in Set.Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) *
      iteratedDerivWithin n f (Set.Ici 0) t = f x - L := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · -- Base case: n = 1, integrand simplifies to -f'(t)
      subst hk
      have hsimpl :
          (fun t => (-1 : ℝ) ^ (0 + 1) / ↑(0 + 1 - 1).factorial *
            (t - x) ^ (0 + 1 - 1) *
            iteratedDerivWithin (0 + 1) f (Set.Ici 0) t) =
          (fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t) := by
        ext t; simp
      rw [hsimpl]
      have hintx : IntegrableOn
          (fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t)
          (Set.Ioi x) :=
        (hcm.neg_deriv_integrableOn hL).mono_set (Set.Ioi_subset_Ioi hx)
      refine tendsto_nhds_unique
        (intervalIntegral_tendsto_integral_Ioi x hintx Filter.tendsto_id) ?_
      simp only [id]
      refine Filter.Tendsto.congr' ?_ (Tendsto.sub tendsto_const_nhds hL)
      filter_upwards [Filter.eventually_gt_atTop (max x 1)] with T hT
      have hxT : x < T := lt_of_le_of_lt (le_max_left x 1) hT
      rw [show (∫ t in x..T, -iteratedDerivWithin 1 f (Set.Ici 0) t) =
          ∫ t in x..T, -iteratedDerivWithin 1 f (Set.Icc x T) t from by
        apply intervalIntegral.integral_congr_ae
        apply ae_of_all volume; intro t ht
        rw [uIoc_of_le (le_of_lt hxT)] at ht
        have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
        have hcda : ContDiffAt ℝ (↑1 : WithTop ℕ∞) f t :=
          (hcm.1.of_le (nat_le_coe_top _)).contDiffAt (Ici_mem_nhds ht_pos)
        congr 1
        rw [iteratedDerivWithin_eq_iteratedDeriv
            (uniqueDiffOn_Icc hxT) hcda (Ioc_subset_Icc_self ht),
          iteratedDerivWithin_eq_iteratedDeriv
            (uniqueDiffOn_Ici 0) hcda
            (Set.mem_Ici.mpr (le_of_lt ht_pos))]]
      exact hcm.integral_neg_deriv x T hx hxT
    · -- Inductive step: n = k + 1 with k ≥ 1. IBP + boundary decay.
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have ih_applied := ih hk1
      simp only [show k + 1 - 1 = k from by omega]
      have hintk := ibp_kernel_integrableOn f hcm k hk1 x hx L hL
      have hintkp1 := ibp_kernel_integrableOn f hcm (k + 1) (by omega) x hx L hL
      simp only [show k + 1 - 1 = k from by omega] at hintkp1
      have hibp := fun T (hT : x < T) => ibp_finite_interval f hcm k hk x T hx hT
      have hbdry := boundary_term_decay f hcm k hk x hx L hL
      have htend_k : Filter.Tendsto (fun T => ∫ t in x..T,
          (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Set.Ici 0) t) Filter.atTop (nhds (f x - L)) := by
        rw [← ih_applied]; exact intervalIntegral_tendsto_integral_Ioi x hintk tendsto_id
      have hsign : ∀ T, ∫ t in x..T,
          (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Set.Ici 0) t =
          -(∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Set.Ici 0) t) := by
        intro T; rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr_ae; apply ae_of_all; intro t _
        have : (-1 : ℝ) ^ (k + 1) = (-1) ^ k * (-1) := pow_succ (-1) k; rw [this]; ring
      have htend_sum : Filter.Tendsto (fun T =>
          (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
            iteratedDerivWithin k f (Set.Ici 0) T +
          ∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
            iteratedDerivWithin k f (Set.Ici 0) t) Filter.atTop (nhds (f x - L)) := by
        simpa [zero_add] using hbdry.add htend_k
      have htend_via_ibp : Filter.Tendsto (fun T => ∫ t in x..T,
          (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
          iteratedDerivWithin (k + 1) f (Set.Ici 0) t) Filter.atTop (nhds (f x - L)) :=
        Tendsto.congr' (Filter.Eventually.mono (Filter.eventually_gt_atTop x) fun T hxT => by
          have := hibp T hxT; linarith [hsign T]) htend_sum
      exact tendsto_nhds_unique
        ((intervalIntegral_tendsto_integral_Ioi x hintkp1 tendsto_id).congr
          (fun T => by simp [id])) htend_via_ibp

lemma chafai_identity (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    f x - L = ∫ p, bernstein_kernel n x p ∂(cm_rescaled f n) := by
  have hn0 : n ≠ 0 := by omega
  have step1 : ∫ p, bernstein_kernel n x p ∂(cm_rescaled f n) =
      ∫ t, bernstein_kernel n x (((n : ℝ) - 1) / t) ∂(cm_measure f n) := by
    unfold cm_rescaled
    exact integral_map_of_stronglyMeasurable (cm_rescaling_measurable n)
      (show Measurable (bernstein_kernel n x) by
        unfold bernstein_kernel; split_ifs
        · exact measurable_const
        · show Measurable fun p : ℝ =>
              (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1)
          fun_prop).stronglyMeasurable
  have step2 : ∫ t, bernstein_kernel n x (((n : ℝ) - 1) / t) ∂(cm_measure f n) =
      ∫ t in Set.Ioi 0,
        bernstein_kernel n x (((n : ℝ) - 1) / t) * cm_density f n t := by
    unfold cm_measure
    have hcont_density : ContinuousOn (cm_density f n) (Set.Ici 0) := by
      unfold cm_density; simp only [hn0, ↓reduceIte]
      exact ((continuousOn_const.mul
        ((continuousOn_pow _).mono fun _ _ => trivial)).mul
        (hcm.1.continuousOn_iteratedDerivWithin (nat_le_coe_top _) (uniqueDiffOn_Ici 0)))
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (AEMeasurable.ennreal_ofReal
        ((hcont_density.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
          measurableSet_Ioi |>.aemeasurable))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact setIntegral_congr_ae measurableSet_Ioi
      (ae_of_all _ fun t ht => by
        simp only [smul_eq_mul, Set.mem_Ioi] at ht ⊢
        rw [ENNReal.toReal_ofReal (cm_density_nonneg hcm n t ht)]; ring)
  have step3 := chafai_kernel_density_eq f hcm n hn x hx
  have step4 := chafai_repeated_ibp f hcm n (by omega) x hx L hL
  linarith

/-- **Subsequential weak limit extraction** for finite measures.

Given a sequence `σ` of finite measures on `ℝ` with uniformly bounded mass
and supported on `[0,∞)`, there exists a subsequence converging weakly to
a limit `μ₀` that is also finite, supported on `[0,∞)`, and satisfies
`∫ g dσ_{φ(k)} → ∫ g dμ₀` for every bounded continuous `g`.

This encapsulates the Prokhorov extraction argument:
- Tightness from support on `[0,∞)` + mass bound (take `K_m = Icc 0 m`)
- Prokhorov compactness (`isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le`)
- Sequential compactness extraction
- Portmanteau for the support condition -/
-- Helper: ↑(normalize μ)(A) ≤ ↑μ(A) when mass ≥ 1
private lemma normalize_le (μ : FiniteMeasure ℝ) (hμ : μ ≠ 0)
    (hm : 1 ≤ μ.mass) (A : Set ℝ) :
    (↑μ.normalize : Measure ℝ) A ≤ (↑μ : Measure ℝ) A := by
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero μ hμ, Measure.smul_apply]
  change (↑(μ.mass⁻¹) : ENNReal) * (↑μ : Measure ℝ) A ≤ (↑μ : Measure ℝ) A
  exact mul_le_of_le_one_left (zero_le _)
    (ENNReal.coe_le_coe.mpr (inv_le_one_of_one_le₀ hm))

-- Helper: compact → seq compact for ProbabilityMeasure ℝ
private lemma prob_seq_compact (S : Set (ProbabilityMeasure ℝ)) (hS : IsCompact S) :
    IsSeqCompact S :=
  isCompact_iff_isSeqCompact.mp hS

/-- The bounded continuous function `p ↦ e^{-x·max(p,0)}`, which agrees with
`p ↦ e^{-xp}` on `[0,∞)` and is bounded by 1. Used to apply weak convergence
of measures supported on `[0,∞)` to the Laplace kernel. -/
private noncomputable def exp_bcf (x : ℝ) (hx : 0 ≤ x) : BoundedContinuousFunction ℝ ℝ where
  toFun p := Real.exp (-(x * max p 0))
  continuous_toFun := by
    apply Continuous.rexp; apply Continuous.neg
    exact continuous_const.mul (continuous_id.max continuous_const)
  map_bounded' := by
    use 2; intro p q
    simp only [dist_eq_norm, Real.norm_eq_abs]
    have h1 : Real.exp (-(x * max p 0)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx (le_max_right _ _)))
    have h2 : Real.exp (-(x * max q 0)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx (le_max_right _ _)))
    rw [abs_le]; constructor <;> linarith [Real.exp_pos (-(x * max p 0)),
      Real.exp_pos (-(x * max q 0))]

/-- `exp_bcf x hx p = e^{-xp}` for `p ≥ 0`. -/
private lemma exp_bcf_eq (x : ℝ) (hx : 0 ≤ x) (p : ℝ) (hp : 0 ≤ p) :
    exp_bcf x hx p = Real.exp (-(x * p)) := by
  simp [exp_bcf, max_eq_left hp]

/-- The integral of `exp_bcf` equals the integral of `e^{-xp}` for measures
supported on `[0,∞)`. -/
private lemma integral_exp_bcf_eq {μ : Measure ℝ} (hsupp : μ (Set.Iio 0) = 0)
    (x : ℝ) (hx : 0 ≤ x) :
    ∫ p, exp_bcf x hx p ∂μ = ∫ p, Real.exp (-(x * p)) ∂μ := by
  apply MeasureTheory.integral_congr_ae
  refine ae_iff.mpr (measure_mono_null ?_ hsupp)
  intro p hp
  simp only [Set.mem_setOf_eq, Set.mem_Iio] at *
  by_contra h; push_neg at h
  exact hp (exp_bcf_eq x hx p h)

lemma finite_measure_subseq_limit
    (σ : ℕ → Measure ℝ) (C : ℝ)
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hmass : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal C)
    (hsupp : ∀ n, (σ n) (Set.Iio 0) = 0)
    (htight : ∀ ε, 0 < ε → ∃ K : ℝ, ∀ n, (σ n) (Set.Ioi K) ≤ ENNReal.ofReal ε) :
    ∃ (μ₀ : Measure ℝ) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧
      μ₀ (Set.Iio 0) = 0 ∧
      μ₀ Set.univ ≤ ENNReal.ofReal C ∧
      ∀ (g : BoundedContinuousFunction ℝ ℝ), Tendsto (fun k => ∫ p, g p ∂(σ (φ k))) atTop
        (nhds (∫ p, g p ∂μ₀)) := by
  let ν : ℕ → FiniteMeasure ℝ := fun n =>
    ⟨σ n + Measure.dirac (-1), MeasureTheory.isFiniteMeasureAdd⟩
  let π : ℕ → ProbabilityMeasure ℝ := fun n => (ν n).normalize
  have h_mass_ge_one : ∀ n, (1 : NNReal) ≤ (ν n).mass := by
    intro n
    change (1 : NNReal) ≤ ((σ n + Measure.dirac (-1) : Measure ℝ) Set.univ).toNNReal
    rw [Measure.add_apply]
    simp only [Measure.dirac_apply, Set.indicator_apply, Set.mem_univ, Pi.one_apply, ite_true]
    have htop : (σ n) Set.univ + 1 ≠ (⊤ : ENNReal) :=
      ENNReal.add_ne_top.2 ⟨measure_ne_top (σ n) Set.univ, by simp⟩
    have hle : (1 : ENNReal) ≤ (σ n) Set.univ + 1 := by
      simp [add_comm]
    simpa using ENNReal.toNNReal_mono htop hle
  have h_mass_le : ∀ n, ((ν n).mass : ℝ) ≤ max C 0 + 1 := by
    intro n
    have h1 : (((ν n).mass : ENNReal)).toReal = ((ν n).mass : ℝ) := by
      rfl
    rw [← h1, FiniteMeasure.ennreal_mass]
    change ((σ n + Measure.dirac (-1) : Measure ℝ) Set.univ).toReal ≤ max C 0 + 1
    rw [Measure.add_apply]
    simp only [Measure.dirac_apply, Set.indicator_apply, Set.mem_univ, Pi.one_apply, ite_true]
    rw [ENNReal.toReal_add (measure_ne_top (σ n) Set.univ) ENNReal.one_ne_top,
      ENNReal.toReal_one]
    exact add_le_add
      (ENNReal.toReal_le_of_le_ofReal (by positivity)
        (le_trans (hmass n) (ENNReal.ofReal_le_ofReal (le_max_left C 0))))
      le_rfl
  have h_π_tight :
      IsTightMeasureSet {x : Measure ℝ | ∃ μ ∈ Set.range π, (μ : Measure ℝ) = x} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hεtop : ε = (⊤ : ENNReal)
    · refine ⟨∅, isCompact_empty, ?_⟩
      intro μ hμ
      simp [hεtop]
    · obtain ⟨K, hK⟩ := htight ε.toReal (ENNReal.toReal_pos (ne_of_gt hε) hεtop)
      let K' : ℝ := max K (-1)
      refine ⟨Set.Icc (-1) K', isCompact_Icc, ?_⟩
      intro μ hμ
      rcases hμ with ⟨μ', hμ', rfl⟩
      rcases hμ' with ⟨n, rfl⟩
      have hν_nonzero_mass : (ν n).mass ≠ 0 := by
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one (h_mass_ge_one n))
      have hν_nonzero : ν n ≠ 0 := (FiniteMeasure.mass_nonzero_iff (ν n)).mp hν_nonzero_mass
      have hneg : ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Set.Iio (-1)) = 0 := by
        change (σ n + Measure.dirac (-1) : Measure ℝ) (Set.Iio (-1)) = 0
        rw [Measure.add_apply]
        have hσ : σ n (Set.Iio (-1)) = 0 := by
          apply le_antisymm _ (zero_le _)
          calc
            σ n (Set.Iio (-1)) ≤ σ n (Set.Iio 0) := by
              refine measure_mono ?_
              intro x hx
              simpa [Set.mem_Iio] using (lt_trans hx (by norm_num : (-1 : ℝ) < 0))
            _ = 0 := hsupp n
        have hδ : (Measure.dirac (-1) : Measure ℝ) (Set.Iio (-1)) = 0 := by
          simp
        simp [hσ, hδ]
      have htail : ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Set.Ioi K') = σ n (Set.Ioi K') := by
        change (σ n + Measure.dirac (-1) : Measure ℝ) (Set.Ioi K') = σ n (Set.Ioi K')
        rw [Measure.add_apply]
        have hδ : (Measure.dirac (-1) : Measure ℝ) (Set.Ioi K') = 0 := by
          have hnot : (-1 : ℝ) ∉ Set.Ioi K' := by
            exact not_lt_of_ge (le_max_right K (-1))
          simp [hnot]
        simp [hδ]
      have hsubset : (Set.Icc (-1) K')ᶜ ⊆ Set.Iio (-1) ∪ Set.Ioi K' := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le, Set.mem_union, Set.mem_Iio,
          Set.mem_Ioi] at hx ⊢
        exact hx
      calc
        ((π n : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Icc (-1) K')ᶜ
            ≤ ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Set.Icc (-1) K')ᶜ := by
              simpa using normalize_le (ν n) hν_nonzero (h_mass_ge_one n) ((Set.Icc (-1) K')ᶜ)
        _ ≤ ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Set.Iio (-1) ∪ Set.Ioi K') :=
            measure_mono hsubset
        _ ≤ ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Set.Iio (-1)) +
              ((ν n : FiniteMeasure ℝ) : Measure ℝ) (Set.Ioi K') :=
            measure_union_le _ _
        _ = σ n (Set.Ioi K') := by rw [hneg, zero_add, htail]
        _ ≤ σ n (Set.Ioi K) := by
            refine measure_mono ?_
            intro x hx
            exact lt_of_le_of_lt (le_max_left K (-1)) hx
        _ ≤ ENNReal.ofReal ε.toReal := hK n
        _ = ε := by rw [ENNReal.ofReal_toReal hεtop]
  have h_compact : IsCompact (closure (Set.range π)) :=
    isCompact_closure_of_isTightMeasureSet h_π_tight
  have h_seq : IsSeqCompact (closure (Set.range π)) := h_compact.isSeqCompact
  have hfreq : ∃ᶠ n in atTop, π n ∈ closure (Set.range π) := by
    refine Filter.Eventually.frequently ?_
    exact Filter.Eventually.of_forall (fun n => subset_closure (Set.mem_range_self n))
  obtain ⟨π₀, -, φ₁, hφ₁, h_tendsto_π⟩ := h_seq.subseq_of_frequently_in hfreq
  let m : ℕ → ℝ := fun k => ((ν (φ₁ k)).mass : ℝ)
  have h_m_mem : ∀ k, m k ∈ Set.Icc 1 (max C 0 + 1) := by
    intro k
    constructor
    · exact_mod_cast (h_mass_ge_one (φ₁ k))
    · simpa [m] using h_mass_le (φ₁ k)
  have hfreq_m : ∃ᶠ k in atTop, m k ∈ Set.Icc 1 (max C 0 + 1) := by
    refine Filter.Eventually.frequently ?_
    exact Filter.Eventually.of_forall h_m_mem
  obtain ⟨M, hM_mem, φ₂, hφ₂, hm_tendsto⟩ :=
    isCompact_Icc.isSeqCompact.subseq_of_frequently_in hfreq_m
  let Φ : ℕ → ℕ := φ₁ ∘ φ₂
  have hΦ : StrictMono Φ := StrictMono.comp hφ₁ hφ₂
  have h_tendsto_π_Φ : Tendsto (fun k => π (Φ k)) atTop (nhds π₀) := by
    simpa [Φ, Function.comp] using h_tendsto_π.comp (StrictMono.tendsto_atTop hφ₂)
  have hm_tendsto_Φ : Tendsto (fun k => ((ν (Φ k)).mass : ℝ)) atTop (nhds M) := by
    simpa [m, Φ, Function.comp] using hm_tendsto
  have hM_nonneg : 0 ≤ M := le_trans zero_le_one hM_mem.1
  let Mnn : NNReal := ⟨M, hM_nonneg⟩
  let ν₀ : FiniteMeasure ℝ := Mnn • π₀.toFiniteMeasure
  let ν₀m : Measure ℝ := (ν₀ : FiniteMeasure ℝ)
  have h_int_bcf : ∀ (g : BoundedContinuousFunction ℝ ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ],
      Integrable g μ := by
    intro g μ _
    apply MeasureTheory.Integrable.mono' (integrable_const ‖g‖)
    · exact g.continuous.aestronglyMeasurable
    · filter_upwards with x
      exact g.norm_coe_le_norm x
  have h_int_lim : ∀ (g : BoundedContinuousFunction ℝ ℝ),
      Tendsto (fun k => ∫ p, g p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ)) atTop
        (nhds (∫ p, g p ∂ν₀m)) := by
    intro g
    have h_π_lim :
        Tendsto (fun k => ∫ p, g p ∂((π (Φ k) : ProbabilityMeasure ℝ) : Measure ℝ)) atTop
          (nhds (∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ))) :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h_tendsto_π_Φ) g
    have h_prod := Tendsto.mul hm_tendsto_Φ h_π_lim
    have h_eq :
        ∀ k, ((ν (Φ k)).mass : ℝ) *
            ∫ p, g p ∂((π (Φ k) : ProbabilityMeasure ℝ) : Measure ℝ) =
            ∫ p, g p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) := by
      intro k
      have hν_nonzero_mass : (ν (Φ k)).mass ≠ 0 := by
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one (h_mass_ge_one (Φ k)))
      have hν_nonzero : ν (Φ k) ≠ 0 :=
        (FiniteMeasure.mass_nonzero_iff (ν (Φ k))).mp hν_nonzero_mass
      have h1 :
          ∫ p, g p ∂((π (Φ k) : ProbabilityMeasure ℝ) : Measure ℝ) =
            ((ν (Φ k)).mass : ℝ)⁻¹ *
              ∫ p, g p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) := by
        rw [show π (Φ k) = (ν (Φ k)).normalize by rfl]
        rw [(ν (Φ k)).toMeasure_normalize_eq_of_nonzero hν_nonzero]
        change ∫ p, g p ∂((((ν (Φ k)).mass⁻¹ : NNReal) : ENNReal) •
            ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ)) = _
        rw [MeasureTheory.integral_smul_measure g
          ((((ν (Φ k)).mass⁻¹ : NNReal) : ENNReal))]
        simp [smul_eq_mul]
      rw [h1]
      have hmass_ne : ((ν (Φ k)).mass : ℝ) ≠ 0 := by
        exact_mod_cast hν_nonzero_mass
      field_simp [hmass_ne]
    simp_rw [h_eq] at h_prod
    have hν₀_eq :
        (M : ℝ) * ∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
          ∫ p, g p ∂ν₀m := by
      change (Mnn : ℝ) * ∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
        ∫ p, g p ∂((ν₀ : FiniteMeasure ℝ) : Measure ℝ)
      change (Mnn : ℝ) * ∫ p, g p ∂((π₀ : ProbabilityMeasure ℝ) : Measure ℝ) =
        ∫ p, g p ∂(((Mnn : ENNReal)) • ((π₀ : ProbabilityMeasure ℝ) : Measure ℝ))
      rw [MeasureTheory.integral_smul_measure g ((Mnn : ENNReal))]
      simp [smul_eq_mul]
    exact hν₀_eq ▸ h_prod
  let χ : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (min 1 (x + 1)), by fun_prop⟩
      1
      (by
        intro x y
        set fx : ℝ := max 0 (min 1 (x + 1))
        set fy : ℝ := max 0 (min 1 (y + 1))
        have hx0 : 0 ≤ fx := by simp [fx]
        have hy0 : 0 ≤ fy := by simp [fy]
        have hx1 : fx ≤ 1 := by simp [fx, zero_le_one]
        have hy1 : fy ≤ 1 := by simp [fy, zero_le_one]
        change |fx - fy| ≤ 1
        rw [abs_le]
        constructor <;> linarith)
  let f_cut : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (min (x + 1) (-x)), by fun_prop⟩
      1
      (by
        intro x y
        set fx : ℝ := max 0 (min (x + 1) (-x))
        set fy : ℝ := max 0 (min (y + 1) (-y))
        have hx0 : 0 ≤ fx := by simp [fx]
        have hy0 : 0 ≤ fy := by simp [fy]
        have hx1 : fx ≤ 1 := by
          have hmin : min (x + 1) (-x) ≤ 1 := by
            by_cases hx : x ≤ 0
            · exact le_trans (min_le_left _ _) (by linarith)
            · exact le_trans (min_le_right _ _) (by linarith)
          simp [fx, hmin, zero_le_one]
        have hy1 : fy ≤ 1 := by
          have hmin : min (y + 1) (-y) ≤ 1 := by
            by_cases hy : y ≤ 0
            · exact le_trans (min_le_left _ _) (by linarith)
            · exact le_trans (min_le_right _ _) (by linarith)
          simp [fy, hmin, zero_le_one]
        change |fx - fy| ≤ 1
        rw [abs_le]
        constructor <;> linarith)
  let h_cut : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (min 1 (-x - 1)), by fun_prop⟩
      1
      (by
        intro x y
        set fx : ℝ := max 0 (min 1 (-x - 1))
        set fy : ℝ := max 0 (min 1 (-y - 1))
        have hx0 : 0 ≤ fx := by simp [fx]
        have hy0 : 0 ≤ fy := by simp [fy]
        have hx1 : fx ≤ 1 := by simp [fx, zero_le_one]
        have hy1 : fy ≤ 1 := by simp [fy, zero_le_one]
        change |fx - fy| ≤ 1
        rw [abs_le]
        constructor <;> linarith)
  have hχ_nonneg : ∀ x, 0 ≤ χ x := by
    intro x
    change 0 ≤ max 0 (min 1 (x + 1))
    exact le_max_left _ _
  have hχ_eq_one : ∀ x, 0 ≤ x → χ x = 1 := by
    intro x hx
    change max 0 (min 1 (x + 1)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hχ_neg1 : χ (-1) = 0 := by
    change max 0 (min 1 ((-1 : ℝ) + 1)) = 0
    norm_num
  have hf_cut_zero_of_nonneg : ∀ x, 0 ≤ x → f_cut x = 0 := by
    intro x hx
    change max 0 (min (x + 1) (-x)) = 0
    have hmin : min (x + 1) (-x) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
    exact max_eq_left hmin
  have hh_cut_zero_of_nonneg : ∀ x, 0 ≤ x → h_cut x = 0 := by
    intro x hx
    change max 0 (min 1 (-x - 1)) = 0
    have hmin : min 1 (-x - 1) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
    exact max_eq_left hmin
  have hν_f_zero : ∀ k, ∫ p, f_cut p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = 0 := by
    intro k
    rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) by rfl]
    rw [MeasureTheory.integral_add_measure (h_int_bcf f_cut (σ (Φ k)))
      (h_int_bcf f_cut (Measure.dirac (-1)))]
    have hσ : ∫ p, f_cut p ∂(σ (Φ k)) = 0 := by
      apply MeasureTheory.integral_eq_zero_of_ae
      refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
      intro p hp
      simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
      by_contra hpneg
      exact hp (hf_cut_zero_of_nonneg p (le_of_not_gt hpneg))
    have hδ : ∫ p, f_cut p ∂(Measure.dirac (-1)) = 0 := by
      rw [MeasureTheory.integral_dirac]
      change max 0 (min (((-1 : ℝ) + 1)) (-(-1 : ℝ))) = 0
      norm_num
    simp [hσ, hδ]
  have hν_h_zero : ∀ k, ∫ p, h_cut p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = 0 := by
    intro k
    rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) by rfl]
    rw [MeasureTheory.integral_add_measure (h_int_bcf h_cut (σ (Φ k)))
      (h_int_bcf h_cut (Measure.dirac (-1)))]
    have hσ : ∫ p, h_cut p ∂(σ (Φ k)) = 0 := by
      apply MeasureTheory.integral_eq_zero_of_ae
      refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
      intro p hp
      simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
      by_contra hpneg
      exact hp (hh_cut_zero_of_nonneg p (le_of_not_gt hpneg))
    have hδ : ∫ p, h_cut p ∂(Measure.dirac (-1)) = 0 := by
      rw [MeasureTheory.integral_dirac]
      change max 0 (min 1 (-(-1 : ℝ) - 1)) = 0
      norm_num
    simp [hσ, hδ]
  have hν₀_ae_zero_f : f_cut =ᵐ[ν₀m] 0 := by
    have hlim := h_int_lim f_cut
    simp_rw [hν_f_zero] at hlim
    have hint0 : ∫ p, f_cut p ∂ν₀m = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun p => by
      change 0 ≤ max 0 (min (p + 1) (-p))
      exact le_max_left _ _)) (h_int_bcf f_cut ν₀m)).mp hint0
  have hν₀_ae_zero_h : h_cut =ᵐ[ν₀m] 0 := by
    have hlim := h_int_lim h_cut
    simp_rw [hν_h_zero] at hlim
    have hint0 : ∫ p, h_cut p ∂ν₀m = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
    exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun p => by
      change 0 ≤ max 0 (min 1 (-p - 1))
      exact le_max_left _ _)) (h_int_bcf h_cut ν₀m)).mp hint0
  let μ₀ : Measure ℝ := ν₀m.restrict (Set.Ici 0)
  haveI hν₀m_fin : IsFiniteMeasure ν₀m := by
    dsimp [ν₀m, ν₀]
    exact Measure.smul_finite (π₀ : Measure ℝ) (by simp)
  haveI hμ₀_fin : IsFiniteMeasure μ₀ :=
    (MeasureTheory.isFiniteMeasure_restrict).2 (measure_ne_top ν₀m (Set.Ici 0))
  refine ⟨μ₀, Φ, hμ₀_fin, hΦ, ?_, ?_, ?_⟩
  · rw [show μ₀ = ν₀m.restrict (Set.Ici 0) by rfl, Measure.restrict_apply measurableSet_Iio]
    have : Set.Iio 0 ∩ Set.Ici 0 = (∅ : Set ℝ) := by
      ext x
      simp
    rw [this, measure_empty]
  · have hχ_seq :
        Tendsto (fun k => ∫ p, χ p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ)) atTop
          (nhds (∫ p, χ p ∂ν₀m)) := h_int_lim χ
    have hχ_sigma : ∀ k, ∫ p, χ p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) =
        ((σ (Φ k)) Set.univ).toReal := by
      intro k
      rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) by rfl]
      rw [MeasureTheory.integral_add_measure (h_int_bcf χ (σ (Φ k)))
        (h_int_bcf χ (Measure.dirac (-1)))]
      have hσ : ∫ p, χ p ∂(σ (Φ k)) = ((σ (Φ k)) Set.univ).toReal := by
        have hEq : χ =ᵐ[σ (Φ k)] fun _ => (1 : ℝ) := by
          refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
          intro p hp
          simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
          by_contra hpneg
          exact hp (hχ_eq_one p (le_of_not_gt hpneg))
        rw [MeasureTheory.integral_congr_ae hEq, MeasureTheory.integral_const]
        simp [Measure.real]
      have hδ : ∫ p, χ p ∂(Measure.dirac (-1)) = 0 := by
        rw [MeasureTheory.integral_dirac]
        exact hχ_neg1
      simp [hσ, hδ]
    simp_rw [hχ_sigma] at hχ_seq
    have hχ_neg_ae : χ =ᵐ[ν₀m.restrict (Set.Iio 0)] 0 := by
      change ∀ᵐ p ∂(ν₀m.restrict (Set.Iio 0)), χ p = 0
      rw [ae_restrict_iff' measurableSet_Iio]
      filter_upwards [hν₀_ae_zero_f, hν₀_ae_zero_h] with p hp_f hp_h hp_neg
      by_cases hp_eq : p = -1
      · rw [hp_eq]
        exact hχ_neg1
      · by_cases hp_gt : -1 < p
        · exfalso
          have hpos : 0 < f_cut p := by
            change 0 < max 0 (min (p + 1) (-p))
            have hmin : 0 < min (p + 1) (-p) := by
              refine lt_min ?_ ?_
              · linarith
              · simpa [Set.mem_Iio] using hp_neg
            exact lt_max_of_lt_right hmin
          have hp_f0 : f_cut p = 0 := by simpa using hp_f
          simp [hp_f0] at hpos
        · exfalso
          have hp_le : p ≤ -1 := le_of_not_gt hp_gt
          have hp_lt : p < -1 := lt_of_le_of_ne hp_le hp_eq
          have hpos : 0 < h_cut p := by
            change 0 < max 0 (min 1 (-p - 1))
            have hmin : 0 < min 1 (-p - 1) := by
              apply lt_min
              · norm_num
              · linarith [hp_lt]
            exact lt_max_of_lt_right hmin
          have hp_h0 : h_cut p = 0 := by simpa using hp_h
          simp [hp_h0] at hpos
    have hχ_ν₀ : ∫ p, χ p ∂ν₀m = (μ₀ Set.univ).toReal := by
      have hsplit := MeasureTheory.setIntegral_union (Set.disjoint_left.mpr (by
        intro x hx1 hx2
        exact (not_lt_of_ge hx1) (by simpa [Set.mem_Iio] using hx2))) measurableSet_Iio
        (h_int_bcf χ (ν₀m.restrict (Set.Ici 0))) (h_int_bcf χ (ν₀m.restrict (Set.Iio 0)))
      have hunion : Set.Ici (0 : ℝ) ∪ Set.Iio 0 = Set.univ := by
        ext x
        simp
      have hsplit' : ∫ p, χ p ∂ν₀m =
          ∫ p in Set.Ici 0, χ p ∂ν₀m + ∫ p in Set.Iio 0, χ p ∂ν₀m := by
        calc
          ∫ p, χ p ∂ν₀m = ∫ p in Set.univ, χ p ∂ν₀m := by
            symm
            exact MeasureTheory.setIntegral_univ
          _ = ∫ p in Set.Ici 0 ∪ Set.Iio 0, χ p ∂ν₀m := by rw [hunion]
          _ = ∫ p in Set.Ici 0, χ p ∂ν₀m + ∫ p in Set.Iio 0, χ p ∂ν₀m := hsplit
      have hIio : ∫ p in Set.Iio 0, χ p ∂ν₀m = 0 := by
        simpa using MeasureTheory.integral_eq_zero_of_ae hχ_neg_ae
      have hIci : ∫ p in Set.Ici 0, χ p ∂ν₀m = (μ₀ Set.univ).toReal := by
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (by
          intro p hp
          exact hχ_eq_one p hp)]
        change ∫ p, (1 : ℝ) ∂μ₀ = _
        rw [MeasureTheory.integral_const]
        simp [Measure.real]
      rw [hIio, add_zero] at hsplit'
      exact hsplit'.trans hIci
    rw [hχ_ν₀] at hχ_seq
    have hle_real : ∀ k, ((σ (Φ k)) Set.univ).toReal ≤ max C 0 := by
      intro k
      exact ENNReal.toReal_le_of_le_ofReal (by positivity)
        (le_trans (hmass (Φ k)) (ENNReal.ofReal_le_ofReal (le_max_left C 0)))
    have hlimit : (μ₀ Set.univ).toReal ≤ max C 0 :=
      le_of_tendsto hχ_seq (Filter.Eventually.of_forall hle_real)
    have htop : μ₀ Set.univ ≠ (⊤ : ENNReal) := measure_ne_top μ₀ Set.univ
    rw [← ENNReal.ofReal_toReal htop]
    refine le_trans (ENNReal.ofReal_le_ofReal hlimit) ?_
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero]
    exact max_le_iff.mpr ⟨le_rfl, zero_le _⟩
  · intro g
    let gχ : BoundedContinuousFunction ℝ ℝ := g * χ
    have hσ_eq : ∀ k,
        ∫ p, g p ∂(σ (Φ k)) =
          ∫ p, gχ p ∂((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) := by
      intro k
      rw [show ((ν (Φ k) : FiniteMeasure ℝ) : Measure ℝ) = σ (Φ k) + Measure.dirac (-1) by rfl]
      rw [MeasureTheory.integral_add_measure (h_int_bcf gχ (σ (Φ k)))
        (h_int_bcf gχ (Measure.dirac (-1)))]
      have hσ : ∫ p, gχ p ∂(σ (Φ k)) = ∫ p, g p ∂(σ (Φ k)) := by
        apply MeasureTheory.integral_congr_ae
        refine ae_iff.mpr (measure_mono_null ?_ (hsupp (Φ k)))
        intro p hp
        simp only [Set.mem_setOf_eq, Set.mem_Iio] at hp ⊢
        by_contra hpneg
        apply hp
        change g p * χ p = g p
        rw [hχ_eq_one p (le_of_not_gt hpneg), mul_one]
      have hδ : ∫ p, gχ p ∂(Measure.dirac (-1)) = 0 := by
        rw [MeasureTheory.integral_dirac]
        change g (-1) * χ (-1) = 0
        rw [hχ_neg1, mul_zero]
      rw [hσ, hδ]
      simp
    have hlim := h_int_lim gχ
    simp_rw [← hσ_eq] at hlim
    have hχ_neg_ae : χ =ᵐ[ν₀m.restrict (Set.Iio 0)] 0 := by
      change ∀ᵐ p ∂(ν₀m.restrict (Set.Iio 0)), χ p = 0
      rw [ae_restrict_iff' measurableSet_Iio]
      filter_upwards [hν₀_ae_zero_f, hν₀_ae_zero_h] with p hp_f hp_h hp_neg
      by_cases hp_eq : p = -1
      · rw [hp_eq]
        exact hχ_neg1
      · by_cases hp_gt : -1 < p
        · exfalso
          have hpos : 0 < f_cut p := by
            change 0 < max 0 (min (p + 1) (-p))
            have hmin : 0 < min (p + 1) (-p) := by
              refine lt_min ?_ ?_
              · linarith
              · simpa [Set.mem_Iio] using hp_neg
            exact lt_max_of_lt_right hmin
          have hp_f0 : f_cut p = 0 := by simpa using hp_f
          simp [hp_f0] at hpos
        · exfalso
          have hp_le : p ≤ -1 := le_of_not_gt hp_gt
          have hp_lt : p < -1 := lt_of_le_of_ne hp_le hp_eq
          have hpos : 0 < h_cut p := by
            change 0 < max 0 (min 1 (-p - 1))
            have hmin : 0 < min 1 (-p - 1) := by
              apply lt_min
              · norm_num
              · linarith [hp_lt]
            exact lt_max_of_lt_right hmin
          have hp_h0 : h_cut p = 0 := by simpa using hp_h
          simp [hp_h0] at hpos
    have hν₀_eq : ∫ p, gχ p ∂ν₀m = ∫ p, g p ∂μ₀ := by
      have hsplit := MeasureTheory.setIntegral_union (Set.disjoint_left.mpr (by
        intro x hx1 hx2
        exact (not_lt_of_ge hx1) (by simpa [Set.mem_Iio] using hx2))) measurableSet_Iio
        (h_int_bcf gχ (ν₀m.restrict (Set.Ici 0))) (h_int_bcf gχ (ν₀m.restrict (Set.Iio 0)))
      have hunion : Set.Ici (0 : ℝ) ∪ Set.Iio 0 = Set.univ := by
        ext x
        simp
      have hsplit' : ∫ p, gχ p ∂ν₀m =
          ∫ p in Set.Ici 0, gχ p ∂ν₀m + ∫ p in Set.Iio 0, gχ p ∂ν₀m := by
        calc
          ∫ p, gχ p ∂ν₀m = ∫ p in Set.univ, gχ p ∂ν₀m := by
            symm
            exact MeasureTheory.setIntegral_univ
          _ = ∫ p in Set.Ici 0 ∪ Set.Iio 0, gχ p ∂ν₀m := by rw [hunion]
          _ = ∫ p in Set.Ici 0, gχ p ∂ν₀m + ∫ p in Set.Iio 0, gχ p ∂ν₀m := hsplit
      have hIio : ∫ p in Set.Iio 0, gχ p ∂ν₀m = 0 := by
        have hEq : gχ =ᵐ[ν₀m.restrict (Set.Iio 0)] 0 := by
          filter_upwards [hχ_neg_ae] with p hp
          change g p * χ p = 0
          have hp0 : χ p = 0 := by simpa using hp
          rw [hp0, mul_zero]
        simpa using MeasureTheory.integral_eq_zero_of_ae hEq
      have hIci : ∫ p in Set.Ici 0, gχ p ∂ν₀m = ∫ p, g p ∂μ₀ := by
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (by
          intro p hp
          change g p * χ p = g p
          rw [hχ_eq_one p hp, mul_one])]
      rw [hIio, add_zero] at hsplit'
      exact hsplit'.trans hIci
    rw [hν₀_eq] at hlim
    exact hlim

/-- Weak convergence of `e^{-xp}` integrals for measures supported on `[0,∞)`,
via the bounded continuous surrogate `exp_bcf`. -/
lemma tendsto_exp_integral
    (σ : ℕ → Measure ℝ) (φ : ℕ → ℕ) (μ₀ : Measure ℝ)
    (hweak : ∀ (g : BoundedContinuousFunction ℝ ℝ),
      Tendsto (fun k => ∫ p, g p ∂(σ (φ k))) atTop (nhds (∫ p, g p ∂μ₀)))
    (hsupp_σ : ∀ n, (σ n) (Set.Iio 0) = 0)
    (hsupp_μ : μ₀ (Set.Iio 0) = 0)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k => ∫ p, Real.exp (-(x * p)) ∂(σ (φ k))) atTop
      (nhds (∫ p, Real.exp (-(x * p)) ∂μ₀)) := by
  have h1 : ∀ k, ∫ p, Real.exp (-(x * p)) ∂(σ (φ k)) =
      ∫ p, exp_bcf x hx p ∂(σ (φ k)) :=
    fun k => (integral_exp_bcf_eq (hsupp_σ (φ k)) x hx).symm
  have h2 : ∫ p, Real.exp (-(x * p)) ∂μ₀ = ∫ p, exp_bcf x hx p ∂μ₀ :=
    (integral_exp_bcf_eq hsupp_μ x hx).symm
  rw [h2]; exact (hweak (exp_bcf x hx)).congr (fun k => (h1 k).symm)

set_option maxHeartbeats 6400000 in
-- quantitative bound on Bernstein kernel approximation error
/-- **Uniform convergence of the Bernstein kernel** on `[0, ∞)` for fixed `x > 0`:
For any `ε > 0`, eventually in `n`, `|φ_n(x,p) - e^{-xp}| < ε` for ALL `p ≥ 0`.

The proof uses: (1) uniform convergence on `[0, R]` for any `R`, and
(2) exponential tail decay: for `p ≥ R`, both `φ_n(x,p) ≤ e^{-xR+o(1)}` and
`e^{-xp} ≤ e^{-xR}`, so `|φ_n - e^{-xp}| ≤ 2e^{-xR}` which is small for large `R`. -/
private lemma kernel_uniform_conv (x : ℝ) (hx : 0 < x) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p →
      |bernstein_kernel n x p - Real.exp (-(x * p))| < ε := by
  have hkernel_le : ∀ n, 2 ≤ n → ∀ p, 0 ≤ p →
      bernstein_kernel n x p ≤ Real.exp (-(x * p)) := by
    intro n hn p hp
    simp only [bernstein_kernel, show ¬(n ≤ 1) from by omega, ite_false]
    by_cases h : 1 - x * p / ↑(n - 1) ≤ 0
    · simp only [max_eq_right h]
      rw [zero_pow (by omega : n - 1 ≠ 0)]
      exact le_of_lt (Real.exp_pos _)
    · push_neg at h; rw [max_eq_left h.le]
      have hle : 1 - x * p / ↑(n - 1) ≤ Real.exp (-(x * p / ↑(n - 1))) := by
        linarith [Real.add_one_le_exp (-(x * p / ↑(n - 1)))]
      calc (1 - x * p / ↑(n - 1)) ^ (n - 1)
          ≤ (Real.exp (-(x * p / ↑(n - 1)))) ^ (n - 1) := by
            apply pow_le_pow_left₀ h.le hle
        _ = Real.exp (↑(n - 1) * -(x * p / ↑(n - 1))) := by
            rw [← Real.exp_nat_mul]
        _ = Real.exp (-(x * p)) := by
            congr 1
            have : (↑(n - 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            field_simp
  have hkernel_nn : ∀ n p, 0 ≤ bernstein_kernel n x p := by
    intro n p; simp only [bernstein_kernel]; split_ifs <;> positivity
  have htail : Tendsto (fun R => Real.exp (-(x * R))) atTop (nhds 0) := by
    apply Filter.Tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
    exact Filter.tendsto_id.const_mul_atTop hx
  obtain ⟨R₀, hR₀⟩ := Metric.tendsto_atTop.mp htail (ε / 2) (half_pos hε)
  set R := max R₀ 1
  have hR_tail : Real.exp (-(x * R)) < ε / 2 := by
    have h1 := hR₀ R (le_max_left _ _)
    rwa [dist_zero_right, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at h1
  have hunif : ∃ N : ℕ, ∀ n, N ≤ n → ∀ p, 0 ≤ p → p ≤ R →
      |bernstein_kernel n x p - Real.exp (-(x * p))| < ε / 2 := by
    -- Quantitative bound: |(1-u/m)^m - e^{-u}| ≤ u²/(m-u) via log(1-t) ≥ -t-t²/(1-t)
    set C := x * R
    have hR_pos : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₀ 1)
    have hC_pos : 0 < C := mul_pos hx hR_pos
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C + 2 + 2 * C ^ 2 / ε)
    refine ⟨N₀, fun n hn p hp hpR => ?_⟩
    have hn_gt : (↑n : ℝ) > C + 2 + 2 * C ^ 2 / ε :=
      lt_of_lt_of_le hN₀ (Nat.cast_le.mpr hn)
    have haux : 0 ≤ 2 * C ^ 2 / ε := div_nonneg (by positivity) hε.le
    have hn_ge2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) < ↑n by linarith [hC_pos]).le
    have hle := hkernel_le n hn_ge2 p hp
    rw [abs_of_nonpos (by linarith), neg_sub]
    set m := n - 1
    have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr (by omega)
    have hm_eq : (↑m : ℝ) = ↑n - 1 := by
      rw [Nat.cast_sub (show 1 ≤ n by omega)]; simp
    have hxp_nn : 0 ≤ x * p := mul_nonneg hx.le hp
    have hxp_le_C : x * p ≤ C := mul_le_mul_of_nonneg_left hpR hx.le
    have hm_gt_C : C < ↑m := by linarith
    set u := x * p / ↑m with hu_def
    have hu_nn : 0 ≤ u := div_nonneg hxp_nn hm_pos.le
    have hu_lt_1 : u < 1 := by rw [div_lt_one hm_pos]; linarith
    have h1u : 0 < 1 - u := by linarith
    have hkernel_eq : bernstein_kernel n x p = (1 - u) ^ m := by
      simp only [bernstein_kernel, show ¬(n ≤ 1) from by omega, ite_false]
      congr 1; exact max_eq_left (by linarith)
    rw [hkernel_eq]
    set b := ↑m * u ^ 2 / (1 - u) with hb_def
    have hb_nn : 0 ≤ b :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)) h1u.le
    have hmu : ↑m * u = x * p := by simp only [hu_def]; field_simp
    -- Lower bound: (1-u)^m ≥ exp(-xp - b) via log(1-u) ≥ -u - u²/(1-u)
    have hpow_ge : (1 - u) ^ m ≥ Real.exp (-(x * p) - b) := by
      have heq : (1 - u) ^ m = Real.exp (↑m * Real.log (1 - u)) := by
        rw [← Real.rpow_natCast (1 - u) m, Real.rpow_def_of_pos h1u, mul_comm]
      rw [heq]; gcongr
      rw [show -(x * p) - b = ↑m * (-u - u ^ 2 / (1 - u)) from by
        rw [← hmu, hb_def]; ring]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
      have habs : |u| < 1 := by rwa [abs_of_nonneg hu_nn]
      have hlog := Real.abs_log_sub_add_sum_range_le habs 1
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one] at hlog
      rw [abs_of_nonneg hu_nn, show u ^ (1 + 1) = u ^ 2 from by ring] at hlog
      linarith [(abs_le.mp hlog).1]
    -- Chain: exp(-xp) - (1-u)^m ≤ exp(-xp) - exp(-xp-b) ≤ b
    have hstep : Real.exp (-(x * p)) - (1 - u) ^ m ≤ b := by
      suffices h : Real.exp (-(x * p)) - Real.exp (-(x * p) - b) ≤ b from by linarith
      have : Real.exp (-(x * p) - b) = Real.exp (-(x * p)) * Real.exp (-b) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; nlinarith [Real.exp_pos (-(x * p)), Real.exp_pos (-b),
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr hxp_nn), Real.add_one_le_exp (-b)]
    -- b = (xp)²/(m-xp) ≤ C²/(m-C) < ε/2
    have hb_eq : b = (x * p) ^ 2 / (↑m - x * p) := by
      simp only [hb_def, hu_def]; field_simp
    have hm_gt_C' : 0 < ↑m - C := by linarith
    have hb_le : b ≤ C ^ 2 / (↑m - C) := by
      rw [hb_eq]
      exact div_le_div₀ (sq_nonneg C) (sq_le_sq' (by linarith) hxp_le_C)
        hm_gt_C' (by linarith)
    have hfinal : C ^ 2 / (↑m - C) < ε / 2 := by
      rw [div_lt_div_iff₀ hm_gt_C' (by positivity : (0:ℝ) < 2)]
      have h1 : ↑m - C > 2 * C ^ 2 / ε := by linarith [hm_eq]
      have h2 : ε * (↑m - C) > ε * (2 * C ^ 2 / ε) := mul_lt_mul_of_pos_left h1 hε
      rw [mul_div_cancel₀ _ (ne_of_gt hε)] at h2; linarith
    linarith
  obtain ⟨N₁, hN₁⟩ := hunif
  refine ⟨max N₁ 2, fun n hn p hp => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right N₁ 2) hn
  by_cases hpR : p ≤ R
  · linarith [hN₁ n (le_trans (le_max_left _ _) hn) p hp hpR]
  · push_neg at hpR
    have h1 := hkernel_le n hn2 p hp
    rw [abs_of_nonpos (by linarith)]
    have h2 : Real.exp (-(x * p)) ≤ Real.exp (-(x * R)) := by
        apply Real.exp_le_exp_of_le
        linarith [mul_le_mul_of_nonneg_left (le_of_lt hpR) (le_of_lt hx)]
    linarith [hkernel_nn n p]

-- **Kernel approximation error → 0**: For measures `σ_n` supported on `[0,∞)`
-- with uniformly bounded mass, the integral of the difference
-- `φ_{n+2}(x,·) - e^{-x·}` against `σ_n` tends to zero.
--
-- For `x = 0` the integrand is identically 0. For `x > 0`, the convergence
-- `φ_n(x,p) → e^{-xp}` is UNIFORM in `p ∈ [0,∞)` (both functions have exponential
-- tail decay), so `|∫(φ_n - e^{-xp})dσ_n| ≤ sup|φ_n - e^{-xp}| · σ_n(ℝ) → 0`.
set_option maxHeartbeats 3200000 in
-- Uniform convergence bound involves quantitative estimates needing extra heartbeats.
private lemma kernel_approx_error_tendsto
    (σ : ℕ → Measure ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hmass : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal C)
    (hsupp : ∀ n, (σ n) (Set.Iio 0) = 0)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k => ∫ p, (bernstein_kernel (φ k + 2) x p -
        Real.exp (-(x * p))) ∂(σ (φ k))) atTop (nhds 0) := by
  by_cases hx0 : x = 0
  · -- x = 0: integrand = 0 since bernstein_kernel n 0 p = 1 = exp(0) for n ≥ 2
    subst hx0
    suffices h : ∀ k, ∫ p, (bernstein_kernel (φ k + 2) 0 p -
        Real.exp (-(0 * p))) ∂(σ (φ k)) = 0 by
      simp only [h]; exact tendsto_const_nhds
    intro k; apply integral_eq_zero_of_ae; apply ae_of_all; intro p
    simp only [bernstein_kernel, show ¬(φ k + 2 ≤ 1) from by omega, zero_mul,
      zero_div, sub_zero, neg_zero, Real.exp_zero, ite_false]; simp [one_pow]
  · -- x > 0: uniform convergence on [0,∞) + mass bound
    have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Metric.tendsto_atTop]; intro ε hε
    have hmax_pos : 0 < max C 1 := lt_max_of_lt_right one_pos
    obtain ⟨N, hN⟩ := kernel_uniform_conv x hx_pos
      (ε / (2 * max C 1)) (div_pos hε (by positivity))
    use N; intro k hk; rw [dist_zero_right]
    haveI := hfin (φ k)
    have hφk : N ≤ φ k + 2 := le_trans hk (le_trans (hφ.id_le k) (Nat.le_add_right _ _))
    calc ‖∫ p, (bernstein_kernel (φ k + 2) x p - Real.exp (-(x * p))) ∂(σ (φ k))‖
        ≤ ∫ p, ‖bernstein_kernel (φ k + 2) x p - Real.exp (-(x * p))‖ ∂(σ (φ k)) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _, (ε / (2 * max C 1)) ∂(σ (φ k)) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ fun p => norm_nonneg _) (integrable_const _)
          rw [EventuallyLE, ae_iff]
          exact measure_mono_null (fun p hp => by
            simp only [Set.mem_setOf_eq, not_le, Real.norm_eq_abs] at hp
            rw [Set.mem_Iio]; by_contra hge; push_neg at hge
            exact absurd (le_of_lt (hN (φ k + 2) hφk p hge)) (not_le.mpr hp))
            (hsupp (φ k))
      _ = ε / (2 * max C 1) * ((σ (φ k)) Set.univ).toReal := by
          simp [MeasureTheory.integral_const, smul_eq_mul, Measure.real, mul_comm]
      _ ≤ ε / (2 * max C 1) * max C 1 := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (div_pos hε (by positivity)))
          exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hmax_pos)
            (le_trans (hmass (φ k)) (ENNReal.ofReal_le_ofReal (le_max_left C 1)))
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε

/-- The integral `∫ φ_{n+2}(x,p) dσ_n` converges to `∫ e^{-xp} dμ₀` along
the subsequence. Decomposes as:
  `∫ φ_{n_k+2} dσ_{n_k} = ∫ (φ_{n_k+2} - e^{-xp}) dσ_{n_k} + ∫ e^{-xp} dσ_{n_k}`
where the first term → 0 (`kernel_approx_error_tendsto`) and the second
term → `∫ e^{-xp} dμ₀` (`tendsto_exp_integral`). -/
private lemma integral_bernstein_kernel_tendsto
    (σ : ℕ → Measure ℝ) (φ : ℕ → ℕ) (μ₀ : Measure ℝ)
    [IsFiniteMeasure μ₀]
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hφ : StrictMono φ)
    (hweak : ∀ (g : BoundedContinuousFunction ℝ ℝ),
      Tendsto (fun k => ∫ p, g p ∂(σ (φ k))) atTop (nhds (∫ p, g p ∂μ₀)))
    (hmass : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal C)
    (hsupp_σ : ∀ n, (σ n) (Set.Iio 0) = 0)
    (hsupp_μ : μ₀ (Set.Iio 0) = 0)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k => ∫ p, bernstein_kernel (φ k + 2) x p ∂(σ (φ k))) atTop
      (nhds (∫ p, Real.exp (-(x * p)) ∂μ₀)) := by
  -- Strategy: show the difference with ∫ e^{-xp} dσ_{φ(k)} → 0 (kernel error),
  -- and ∫ e^{-xp} dσ_{φ(k)} → ∫ e^{-xp} dμ₀ (weak convergence).
  -- Combined: ∫ φ_{φ(k)+2} dσ_{φ(k)} → ∫ e^{-xp} dμ₀.
  have hterm1 := kernel_approx_error_tendsto (C := C) σ φ hφ hfin hmass hsupp_σ x hx
  have hterm2 := tendsto_exp_integral σ φ μ₀ hweak hsupp_σ hsupp_μ x hx
  -- The sum of a sequence tending to 0 and one tending to L tends to L
  rw [show (∫ p, Real.exp (-(x * p)) ∂μ₀) = 0 + ∫ p, Real.exp (-(x * p)) ∂μ₀ from
    (zero_add _).symm]
  apply Tendsto.congr _ (hterm1.add hterm2)
  intro k; haveI := hfin (φ k)
  -- ∫ (φ - e^{-xp}) dσ + ∫ e^{-xp} dσ = ∫ φ dσ (linearity)
  -- Bernstein kernel is bounded on [0,∞) ⊆ support, hence integrable on finite σ
  have hbk_int : Integrable (fun p => bernstein_kernel (φ k + 2) x p) (σ (φ k)) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · apply Measurable.aestronglyMeasurable
      simp only [bernstein_kernel]
      exact Measurable.ite (measurableSet_le measurable_const measurable_const)
        measurable_const
        ((measurable_const.sub (measurable_id.const_mul x |>.div_const _) |>.max
          measurable_const).pow measurable_const)
    · rw [ae_iff]; apply measure_mono_null (fun p hp => ?_) (hsupp_σ (φ k))
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le, Set.mem_Iio] at *
      by_contra hge; push_neg at hge
      simp only [bernstein_kernel, show ¬(φ k + 2 ≤ 1) from by omega, ite_false,
        show φ k + 2 - 1 = φ k + 1 from by omega] at hp
      have hmax : max (1 - x * p / ↑(φ k + 1)) 0 ≤ 1 := by
        apply max_le _ (by norm_num)
        have : 0 ≤ x * p / ↑(φ k + 1) := div_nonneg (mul_nonneg hx hge) (by positivity)
        linarith
      have : 0 ≤ max (1 - x * p / ↑(φ k + 1)) 0 := le_max_right _ _
      rw [abs_of_nonneg (pow_nonneg this _)] at hp
      linarith [pow_le_one₀ (n := φ k + 1) this hmax]
  have hexp_int : Integrable (fun p => Real.exp (-(x * p))) (σ (φ k)) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact Measurable.aestronglyMeasurable (by fun_prop)
    · rw [ae_iff]; apply measure_mono_null (fun p hp => ?_) (hsupp_σ (φ k))
      simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le, Set.mem_Iio] at *
      by_contra hge; push_neg at hge
      have : Real.exp (-(x * p)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx hge))
      rw [abs_of_pos (Real.exp_pos _)] at hp; linarith
  linarith [MeasureTheory.integral_sub hbk_int hexp_int]

private lemma diagonal_convergence
    (f : ℝ → ℝ) (L : ℝ)
    (σ : ℕ → Measure ℝ) (φ : ℕ → ℕ) (μ₀ : Measure ℝ)
    [IsFiniteMeasure μ₀]
    (hfin : ∀ n, IsFiniteMeasure (σ n))
    (hφ : StrictMono φ)
    (hweak : ∀ (g : BoundedContinuousFunction ℝ ℝ),
      Tendsto (fun k => ∫ p, g p ∂(σ (φ k))) atTop (nhds (∫ p, g p ∂μ₀)))
    (hmass : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal C)
    (hsupp_σ : ∀ n, (σ n) (Set.Iio 0) = 0)
    (hsupp_μ : μ₀ (Set.Iio 0) = 0)
    (x : ℝ) (hx : 0 ≤ x)
    (hident : ∀ n, f x - L = ∫ p, bernstein_kernel (n + 2) x p ∂(σ n)) :
    f x - L = ∫ p, Real.exp (-(x * p)) ∂μ₀ := by
  -- The sequence ∫ φ_{φ(k)+2}(x,p) dσ_{φ(k)} = f(x) - L for all k (constant!)
  have hconst : ∀ k, ∫ p, bernstein_kernel (φ k + 2) x p ∂(σ (φ k)) = f x - L :=
    fun k => (hident (φ k)).symm
  -- The same sequence converges to ∫ e^{-xp} dμ₀
  have htends := integral_bernstein_kernel_tendsto (C := C)
    σ φ μ₀ hfin hφ hweak hmass hsupp_σ hsupp_μ x hx
  -- A constant sequence converging to a limit implies the constant equals the limit
  exact tendsto_nhds_unique (tendsto_const_nhds.congr (fun k => (hconst k).symm)) htends

lemma prokhorov_limit_identification (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (_hL : Filter.Tendsto f Filter.atTop (nhds L)) (_hL_nn : 0 ≤ L)
    (hmass_bound : ∀ n, 2 ≤ n →
      (cm_rescaled f n) Set.univ ≤ ENNReal.ofReal (f 0 - L))
    (hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Set.Iio 0) = 0)
    (hfin : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_rescaled f n))
    (hidentity : ∀ n, 2 ≤ n → ∀ x, 0 ≤ x →
      f x - L = ∫ p, bernstein_kernel n x p ∂(cm_rescaled f n)) :
    ∃ (μ₀ : Measure ℝ), IsFiniteMeasure μ₀ ∧ μ₀ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  -- Shift indices: work with σ(n) = cm_rescaled f (n+2) to avoid the n ≥ 2 condition
  set σ := fun n => cm_rescaled f (n + 2) with hσ_def
  have hfin_σ : ∀ n, IsFiniteMeasure (σ n) := fun n => hfin (n + 2) (by omega)
  have hmass_σ : ∀ n, (σ n) Set.univ ≤ ENNReal.ofReal (f 0 - L) :=
    fun n => hmass_bound (n + 2) (by omega)
  have hsupp_σ : ∀ n, (σ n) (Set.Iio 0) = 0 := fun n => hsupp (n + 2) (by omega)
  have hident_σ : ∀ n, 2 ≤ n + 2 → ∀ x, 0 ≤ x →
      f x - L = ∫ p, bernstein_kernel (n + 2) x p ∂(σ n) :=
    fun n hn2 x hx => hidentity (n + 2) hn2 x hx
  -- Step 1: Prokhorov extraction — get subsequence σ_{φ(k)} → μ₀
  have htight_σ : ∀ ε, 0 < ε → ∃ K : ℝ, ∀ n, (σ n) (Set.Ioi K) ≤ ENNReal.ofReal ε := by
    /- Tightness from CM structure (genuinely >30 lines):
       For ε > 0, choose x₀ = 1/K for large K (continuity of f at 0 gives
       f(0) - f(1/K) < ε(1 - e⁻¹)). From hident_σ with x = 0:
       toReal(σ_n(univ)) = f(0) - L (exact mass). With x = 1/K:
       f(1/K) - L = ∫ φ_{n+2}(1/K, p) dσ_n. The difference:
       ∫ (1 - φ_{n+2}(1/K, p)) dσ_n = f(0) - f(1/K).
       For p > K: φ_{n+2}(1/K, p) = max(1-(p/K)/(n+1), 0)^{n+1}
       ≤ exp(-p/K) ≤ exp(-1) (by one_sub_div_pow_le_exp_neg),
       so 1 - φ ≥ 1 - e⁻¹. Therefore:
       (1 - e⁻¹) · toReal(σ_n(Ioi K)) ≤ ∫_{Ioi K} (1-φ) dσ_n
       ≤ ∫ (1-φ) dσ_n = f(0) - f(1/K) < ε(1 - e⁻¹).
       So toReal(σ_n(Ioi K)) < ε, hence σ_n(Ioi K) ≤ ENNReal.ofReal ε.
       Blocking: the ℝ-integral decomposition ∫(1-φ) = ∫1 - ∫φ requires
       integrability of φ_{n+2} wrt σ_n (bounded measurable on finite measure),
       and the lower bound ∫_{Ioi K}(1-φ) ≥ (1-e⁻¹)·toReal(σ_n(Ioi K))
       requires converting between set integrals and measure evaluations
       via integral_indicator/setIntegral and ENNReal.le_ofReal_iff_toReal_le.
       The continuity-at-0 step needs ContinuousOn.tendsto or Filter.Tendsto
       from hcm.1.continuousOn. Total: ~35 lines. -/
    intro ε hε
    -- Mass identity: (σ n univ).toReal = f 0 - L (from hident at x=0, kernel=1)
    have hmass_real : ∀ n, (σ n Set.univ).toReal = f 0 - L := by
      intro n; haveI := hfin_σ n
      have h1 := hident_σ n (by omega) 0 le_rfl
      simp only [bernstein_kernel, show ¬(n + 2 ≤ 1) from by omega,
        ite_false, zero_mul, zero_div, sub_zero, zero_le_one, max_eq_left,
        one_pow, MeasureTheory.integral_const, smul_eq_mul, mul_one] at h1
      -- h1 : f 0 - L = ∫ 1 dσ_n = (σ_n).real univ
      rw [show (σ n).real Set.univ = (σ n Set.univ).toReal from by
        simp [Measure.real]] at h1
      linarith
    -- Integral bound (sorry): (1-exp(-x₀K)) · toReal(σ_n(Ioi K)) ≤ f(0)-f(x₀)
    have hbound : ∀ (x₀ K : ℝ), 0 < x₀ → 0 < K → ∀ n,
        (1 - Real.exp (-(x₀ * K))) * (σ n (Set.Ioi K)).toReal ≤ f 0 - f x₀ := by
      intro x₀ K hx₀ hK n; haveI := hfin_σ n
      -- f(0)-f(x₀) = mass - ∫ kernel (from hmass_real + hident_σ)
      have h_diff : f 0 - f x₀ = (σ n Set.univ).toReal -
          ∫ p, bernstein_kernel (n + 2) x₀ p ∂(σ n) := by
        linarith [hmass_real n, hident_σ n (by omega) x₀ hx₀.le]
      -- ∫ kernel ≤ mass - (1-exp(-x₀K))·σ(Ioi K).toReal
      -- ↔ (1-exp(-x₀K))·σ(Ioi K).toReal ≤ mass - ∫ kernel = f(0)-f(x₀)
      rw [h_diff]
      -- ∫ kernel ≤ σ(Iic K) + exp(-x₀K)·σ(Ioi K) = σ(univ) - (1-exp(-x₀K))·σ(Ioi K)
      have hmeas : (σ n Set.univ).toReal = (σ n (Set.Iic K)).toReal + (σ n (Set.Ioi K)).toReal := by
        rw [← Set.Iic_union_Ioi,
          measure_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi,
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      set c := Real.exp (-(x₀ * K))
      set g := fun p : ℝ => Set.indicator (Set.Iic K) (fun _ => (1:ℝ)) p +
        Set.indicator (Set.Ioi K) (fun _ => c) p
      have hg_val : ∫ p, g p ∂(σ n) =
          (σ n (Set.Iic K)).toReal + c * (σ n (Set.Ioi K)).toReal := by
        simp only [g]
        rw [integral_add ((integrable_const (1:ℝ)).indicator measurableSet_Iic)
          ((integrable_const c).indicator measurableSet_Ioi),
          integral_indicator_const _ measurableSet_Iic,
          integral_indicator_const _ measurableSet_Ioi,
          Measure.real, Measure.real, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
      have hkernel_int : Integrable (bernstein_kernel (n + 2) x₀) (σ n) := by
        apply Integrable.mono' (integrable_const (1 : ℝ))
        · apply Measurable.aestronglyMeasurable
          unfold bernstein_kernel
          exact Measurable.ite (measurableSet_le measurable_const measurable_const)
            measurable_const
            ((measurable_const.sub (measurable_id.const_mul x₀ |>.div_const _) |>.max
              measurable_const).pow measurable_const)
        · rw [ae_iff]
          apply measure_mono_null (fun p hp => ?_) (hsupp_σ n)
          simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le, Set.mem_Iio] at *
          by_contra hp_nonneg
          push_neg at hp_nonneg
          simp only [bernstein_kernel, show ¬(n + 2 ≤ 1) from by omega, ite_false,
            show n + 2 - 1 = n + 1 from by omega] at hp
          have hmax : max (1 - x₀ * p / ↑(n + 1)) 0 ≤ 1 := by
            apply max_le _ (by norm_num)
            have : 0 ≤ x₀ * p / ↑(n + 1) :=
              div_nonneg (mul_nonneg hx₀.le hp_nonneg) (by positivity)
            linarith
          have : 0 ≤ max (1 - x₀ * p / ↑(n + 1)) 0 := le_max_right _ _
          rw [abs_of_nonneg (pow_nonneg this _)] at hp
          linarith [pow_le_one₀ (n := n + 1) this hmax]
      have hkernel_le_g : bernstein_kernel (n + 2) x₀ ≤ᶠ[MeasureTheory.ae (σ n)] g := by
        have hnonneg_ae : ∀ᵐ p ∂σ n, 0 ≤ p := by
          rw [ae_iff]
          show (σ n) {p : ℝ | ¬0 ≤ p} = 0
          have hset : {p : ℝ | ¬0 ≤ p} = Set.Iio 0 := by
            ext p
            simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
          rw [hset]
          exact hsupp_σ n
        filter_upwards [hnonneg_ae] with p hp_nonneg
        by_cases hpK : p ≤ K
        · have hkernel_le_one : bernstein_kernel (n + 2) x₀ p ≤ 1 := by
            simp only [bernstein_kernel, show ¬(n + 2 ≤ 1) from by omega, ite_false,
              show n + 2 - 1 = n + 1 from by omega]
            have hmax : max (1 - x₀ * p / ↑(n + 1)) 0 ≤ 1 := by
              apply max_le _ (by norm_num)
              have : 0 ≤ x₀ * p / ↑(n + 1) :=
                div_nonneg (mul_nonneg hx₀.le hp_nonneg) (by positivity)
              linarith
            exact pow_le_one₀ (le_max_right _ _) hmax
          have hg_eq : g p = 1 := by
            unfold g
            rw [Set.indicator_of_mem (show p ∈ Set.Iic K from hpK),
              Set.indicator_of_notMem (show p ∉ Set.Ioi K from not_lt.mpr hpK)]
            simp
          simpa [hg_eq] using hkernel_le_one
        · have hpK' : K < p := lt_of_not_ge hpK
          have hkernel_le_exp : bernstein_kernel (n + 2) x₀ p ≤ Real.exp (-(x₀ * p)) := by
            have hxp_nonneg : 0 ≤ x₀ * p := mul_nonneg hx₀.le hp_nonneg
            simp only [bernstein_kernel, show ¬(n + 2 ≤ 1) from by omega, ite_false,
              show n + 2 - 1 = n + 1 from by omega]
            by_cases hxp : x₀ * p ≤ ↑(n + 1)
            · have hmax_eq : max (1 - x₀ * p / ↑(n + 1)) 0 = 1 - x₀ * p / ↑(n + 1) := by
                apply max_eq_left
                have hdiv : x₀ * p / ↑(n + 1) ≤ 1 := by
                  exact (div_le_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))).2 (by simpa using hxp)
                linarith
              rw [hmax_eq]
              simpa using Real.one_sub_div_pow_le_exp_neg (n := n + 1) (t := x₀ * p) hxp
            · have hmax_eq : max (1 - x₀ * p / ↑(n + 1)) 0 = 0 := by
                apply max_eq_right
                push_neg at hxp
                have : 1 < x₀ * p / ↑(n + 1) := by
                  exact (lt_div_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))).2 (by simpa using hxp)
                linarith
              rw [hmax_eq, zero_pow (by positivity)]
              exact le_of_lt (Real.exp_pos _)
          have hexp_le : Real.exp (-(x₀ * p)) ≤ c := by
            dsimp [c]
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul_of_nonneg_left hpK'.le hx₀.le]
          have hg_eq : g p = c := by
            unfold g
            rw [Set.indicator_of_notMem (show p ∉ Set.Iic K from not_le.mpr hpK'),
              Set.indicator_of_mem (show p ∈ Set.Ioi K from hpK')]
            simp
          rw [hg_eq]
          exact hkernel_le_exp.trans hexp_le
      have hle : ∫ p, bernstein_kernel (n+2) x₀ p ∂(σ n) ≤ ∫ p, g p ∂(σ n) := by
        apply integral_mono_ae
          hkernel_int
          ((integrable_const (1:ℝ)).indicator measurableSet_Iic |>.add
            ((integrable_const c).indicator measurableSet_Ioi))
          hkernel_le_g
      linarith
    -- Choose x₀ > 0 with f(0)-f(x₀) < ε/2 (continuity at 0)
    have hx₀ : ∃ x₀ : ℝ, 0 < x₀ ∧ f 0 - f x₀ < ε / 2 := by
      have hcont : ContinuousWithinAt f (Set.Ici 0) 0 :=
        hcm.1.continuousOn.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
      rw [Metric.continuousWithinAt_iff] at hcont
      obtain ⟨δ, hδ, hclose⟩ := hcont (ε / 2) (half_pos hε)
      refine ⟨δ / 2, by positivity, ?_⟩
      have hdist : dist (f (δ/2)) (f 0) < ε / 2 :=
        hclose (Set.mem_Ici.mpr (by positivity)) (by
          rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith)
      rw [Real.dist_eq] at hdist
      rw [show f 0 - f (δ/2) = -(f (δ/2) - f 0) from by ring]
      linarith [neg_abs_le (f (δ/2) - f 0)]
    obtain ⟨x₀, hx₀_pos, hx₀_bound⟩ := hx₀
    -- Choose K = max(1/x₀, 1) so exp(-x₀K) ≤ exp(-1) < 1/2
    refine ⟨max (1 / x₀) 1, fun n => ?_⟩
    -- σ_n(Ioi K) ≤ ofReal ε
    have hK : 0 < max (1 / x₀) 1 := lt_max_of_lt_right one_pos
    have hexp : Real.exp (-(x₀ * max (1 / x₀) 1)) ≤ 1 / 2 := by
      calc Real.exp (-(x₀ * max (1 / x₀) 1))
          ≤ Real.exp (-1) := by
            apply Real.exp_le_exp_of_le; linarith [le_max_left (1/x₀) 1,
              mul_le_mul_of_nonneg_left (le_max_left (1/x₀) 1) hx₀_pos.le,
              div_mul_cancel₀ (1 : ℝ) (ne_of_gt hx₀_pos)]
        _ ≤ 1 / 2 := by
            rw [Real.exp_neg]
            -- 1/e ≤ 1/2 ↔ 2 ≤ e
            rw [inv_le_comm₀ (Real.exp_pos 1) (by positivity : (0:ℝ) < 1/2)]
            linarith [Real.add_one_le_exp (1 : ℝ)]
    have h_toReal_le : (σ n (Set.Ioi (max (1/x₀) 1))).toReal ≤ ε := by
      have h1 := hbound x₀ (max (1/x₀) 1) hx₀_pos hK n
      have h2 : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(x₀ * max (1/x₀) 1)) := by linarith
      have h3 : 0 ≤ (σ n (Set.Ioi (max (1/x₀) 1))).toReal := ENNReal.toReal_nonneg
      nlinarith
    rwa [← ENNReal.ofReal_toReal (ne_of_lt (measure_lt_top (σ n) _)),
      ENNReal.ofReal_le_ofReal_iff hε.le]
  obtain ⟨μ₀, φ, hfin_μ, hφ_mono, hsupp_μ, hmass_μ, hweak⟩ :=
    finite_measure_subseq_limit σ (f 0 - L) hfin_σ hmass_σ hsupp_σ htight_σ
  -- Step 2: Verify the Laplace identity via diagonal convergence
  refine ⟨μ₀, hfin_μ, hsupp_μ, fun t ht => ?_⟩
  -- We need: f t = L + ∫ e^{-tp} dμ₀, i.e., f t - L = ∫ e^{-tp} dμ₀
  have hdiag := diagonal_convergence (C := f 0 - L) f L
    σ φ μ₀ hfin_σ hφ_mono hweak hmass_σ hsupp_σ hsupp_μ t ht
    (fun n => hident_σ n (by omega) t ht)
  linarith

end
