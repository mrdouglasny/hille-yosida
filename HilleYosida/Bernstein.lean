/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bernstein's Theorem

Completely monotone functions on `[0, ∞)` are Laplace transforms of
finite positive measures. This is a key ingredient in the BCR
decomposition: BCR 4.1.13 = Bochner on ℝ^d + Bernstein on [0,∞).

Ref: Bernstein (1928); Widder, "The Laplace Transform" Ch. IV.
Verified correct by Gemini (2026-03-23).
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

noncomputable section

open MeasureTheory Set intervalIntegral Filter

/-- A function `f : ℝ → ℝ` is completely monotone on `[0, ∞)` if it is
C^∞ on `[0, ∞)` and `(-1)^n f^{(n)}(t) ≥ 0` for all `n ∈ ℕ, t ≥ 0`.

This is Widder's definition ("The Laplace Transform", p. 145). It is
equivalent to the forward-difference characterization
`∑_{k=0}^n (-1)^k C(n,k) f(t+kh) ≥ 0`, but the smooth version avoids
a ~500-line bootstrap from differences to derivatives in Lean.

Examples: constants ≥ 0, `e^{-αt}` (α ≥ 0), `1/(t+α)^β` (α,β > 0). -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ f (Set.Ici 0) ∧
  ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
    0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Set.Ici 0) t

/-! ## Basic properties of CM functions -/

/-- A CM function is nonneg (n=0 case). -/
lemma IsCompletelyMonotone.nonneg (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  simpa [iteratedDerivWithin_zero] using hcm.2 0 t ht

/-- A CM function is non-increasing on [0, ∞) (n=1 case gives f' ≤ 0). -/
lemma IsCompletelyMonotone.deriv_nonpos (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Set.Ici 0) t ≤ 0 := by
  have := hcm.2 1 t ht
  simp only [pow_one] at this
  linarith

/-- A CM function is bounded by f(0) on [0, ∞). -/
lemma IsCompletelyMonotone.bounded (hcm : IsCompletelyMonotone f) (t : ℝ) (ht : 0 ≤ t) :
    f t ≤ f 0 := by
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := Ne.symm (ne_of_beq_false rfl)
  have hanti : AntitoneOn f (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcm.1.continuousOn
      ((hcm.1.differentiableOn htop).mono interior_subset)
      (fun x hx => by
        rw [interior_Ici] at hx
        have h1 := hcm.deriv_nonpos x (le_of_lt hx)
        rwa [iteratedDerivWithin_one,
          derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at h1)
  exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht

/-- The sign condition for `-f'` being CM: `(-1)^n D^n(-f') = (-1)^{n+1} D^{n+1}f ≥ 0`.
The smoothness part (ContDiffOn) is blocked on C^ω vs C^∞ mismatch
in `WithTop ℕ∞` and is omitted since this lemma is not used downstream. -/
lemma IsCompletelyMonotone.deriv_cm_sign (hcm : IsCompletelyMonotone f)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n
      (fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t) (Set.Ici 0) t := by
  rw [iteratedDerivWithin_fun_neg, iteratedDerivWithin_one,
    ← iteratedDerivWithin_succ']
  have := hcm.2 (n + 1) t ht
  simp only [pow_succ] at this ⊢
  linarith

/-! ## Taylor integral remainder -/

/-- **Taylor integral remainder** on `[a, b]` (sorry-free). The error of the n-th
Taylor polynomial centered at `a` equals `∫_a^b (b-t)^n/n! · f^{(n+1)}(t) dt`.

This is proved via FTC applied to `t ↦ taylorWithinEval f n s t b`, whose derivative
is `(n!)⁻¹(b-t)^n · f^{(n+1)}(t)` by `hasDerivWithinAt_taylorWithinEval_at_Icc`,
and whose value at `t=b` is `f(b)` by `taylorWithinEval_self`. -/
theorem taylor_integral_remainder {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hab : a < b)
    (hf : ContDiffOn ℝ (↑(n + 1) : WithTop ℕ∞) f (Icc a b)) :
    f b - taylorWithinEval f n (Icc a b) a b =
      ∫ t in a..b, (↑n.factorial)⁻¹ * (b - t) ^ n *
        iteratedDerivWithin (n + 1) f (Icc a b) t := by
  set s := Icc a b
  have hab' := le_of_lt hab
  have hle : (↑n : WithTop ℕ∞) ≤ ↑(n + 1) :=
    WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr (by omega))
  have hlt : (↑n : WithTop ℕ∞) < ↑(n + 1) :=
    WithTop.coe_lt_coe.mpr (ENat.coe_lt_coe.mpr (by omega))
  have huniq := uniqueDiffOn_Icc hab
  have hf_n : ContDiffOn ℝ (↑n : WithTop ℕ∞) f s := hf.of_le hle
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f s) s :=
    hf.differentiableOn_iteratedDerivWithin hlt huniq
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt (fun y => taylorWithinEval f n s y b)
      (((↑n.factorial)⁻¹ * (b - t) ^ n) •
        iteratedDerivWithin (n + 1) f s t) t := by
    intro t ht
    exact (hasDerivWithinAt_taylorWithinEval_at_Icc b hab
      (Ioo_subset_Icc_self ht) hf_n hdiff).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcont : ContinuousOn (fun t => taylorWithinEval f n s t b) s :=
    continuousOn_taylorWithinEval huniq hf_n
  have hint : IntervalIntegrable (fun t => ((↑n.factorial)⁻¹ * (b - t) ^ n) •
      iteratedDerivWithin (n + 1) f s t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab']
    exact (continuousOn_const.mul
      ((continuousOn_const.sub continuousOn_id).pow n)).smul
      (hf.continuousOn_iteratedDerivWithin le_rfl huniq)
  have hftc := integral_eq_sub_of_hasDerivAt_of_le hab' hcont hderiv hint
  simp only [taylorWithinEval_self, smul_eq_mul] at hftc
  linarith

/-- A CM function has a limit at infinity: it is antitone and bounded below by 0,
so `f(t) → L ≥ 0` as `t → ∞`. -/
lemma IsCompletelyMonotone.tendsto_atTop (hcm : IsCompletelyMonotone f) :
    ∃ L, Filter.Tendsto f Filter.atTop (nhds L) ∧ 0 ≤ L := by
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := Ne.symm (ne_of_beq_false rfl)
  have hanti : AntitoneOn f (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hcm.1.continuousOn
      ((hcm.1.differentiableOn htop).mono interior_subset)
      (fun x hx => by
        rw [interior_Ici] at hx
        have h1 := hcm.deriv_nonpos x (le_of_lt hx)
        rwa [iteratedDerivWithin_one,
          derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at h1)
  set g := fun t : ℝ => f (max t 0)
  have hg_anti : Antitone g := fun a b hab =>
    hanti (Set.mem_Ici.mpr (le_max_right _ _))
      (Set.mem_Ici.mpr (le_max_right _ _)) (max_le_max_right 0 hab)
  have hg_bdd : BddBelow (Set.range g) :=
    ⟨0, fun _ ⟨t, ht⟩ => ht ▸ hcm.nonneg _ (le_max_right _ _)⟩
  refine ⟨⨅ i, g i, ?_, le_ciInf (fun t => hcm.nonneg _ (le_max_right _ _))⟩
  exact (tendsto_atTop_ciInf hg_anti hg_bdd).congr'
    (Filter.eventually_atTop.mpr ⟨0, fun t ht => by simp [g, max_eq_left ht]⟩)

/-! ## Set transfer for iterated derivatives -/

/-- `iteratedDerivWithin` on `Icc x T` agrees with `iteratedDerivWithin` on `Ici 0`
at interior points, since both equal `iteratedDeriv n f t` when `0 < t`. -/
lemma iteratedDerivWithin_Icc_eq_Ici {n : ℕ}
    (hcm : IsCompletelyMonotone f)
    {x T t : ℝ} (hx : 0 ≤ x) (hxT : x < T) (ht : t ∈ Set.Ioo x T) :
    iteratedDerivWithin n f (Set.Icc x T) t =
      iteratedDerivWithin n f (Set.Ici 0) t := by
  have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
  have hcda : ContDiffAt ℝ (↑n : WithTop ℕ∞) f t :=
    (hcm.1.of_le le_top).contDiffAt (Ici_mem_nhds ht_pos)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hcda
        (Set.Ioo_subset_Icc_self ht),
      ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
        (Set.mem_Ici.mpr (le_of_lt ht_pos))]

/-- **CM sign condition for Taylor remainder**: For a CM function, the Taylor
integral remainder `∫_x^T (T-t)^{n-1}/(n-1)! f^{(n)}(t) dt` has sign `(-1)^n`.
This connects `taylor_integral_remainder` to the CM condition via
`iteratedDerivWithin_Icc_eq_Ici` (set transfer at interior points) and
`Ioo_ae_eq_Icc` (boundary is Lebesgue-null).

Needs extra heartbeats for ae filter + iteratedDerivWithin reasoning. -/
lemma IsCompletelyMonotone.taylor_nonneg_remainder
    (hcm : IsCompletelyMonotone f) {x T : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hxT : x < T) :
    0 ≤ (-1 : ℝ) ^ n * ∫ t in x..T,
      (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
      iteratedDerivWithin n f (Set.Icc x T) t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_nonneg_of_ae_restrict (le_of_lt hxT)
  have hIoo : ∀ t ∈ Set.Ioo x T, (0 : ℝ) ≤ ((-1 : ℝ) ^ n *
      ((↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
        iteratedDerivWithin n f (Set.Icc x T) t)) := fun t ht =>
    calc (0 : ℝ) ≤ (↑(n - 1).factorial)⁻¹ * (T - t) ^ (n - 1) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Set.Icc x T) t) :=
          mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (pow_nonneg (sub_nonneg.mpr (le_of_lt ht.2)) _))
            (by rw [iteratedDerivWithin_Icc_eq_Ici hcm hx hxT ht]
                exact hcm.2 n t (le_of_lt (lt_of_le_of_lt hx ht.1)))
      _ = _ := by ring
  have h_mem : ∀ᵐ t ∂volume.restrict (Set.Icc x T), t ∈ Set.Ioo x T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact (Ioo_ae_eq_Icc (a := x) (b := T)).mono (fun t h ht => h.mpr ht)
  exact h_mem.mono fun t ht => by simp only [Pi.zero_apply]; exact hIoo t ht

/-! ## Bernstein's Theorem -/

/-- For a CM function `f` on `[0,∞)`, the n=1 Taylor integral remainder gives
`f(x) - f(T) = ∫_x^T (-f'(t)) dt`, where the integrand is nonneg by the CM condition.
This shows `f` is the integral of its (nonneg) negative derivative. -/
lemma IsCompletelyMonotone.integral_neg_deriv (hcm : IsCompletelyMonotone f)
    (x T : ℝ) (hx : 0 ≤ x) (hxT : x < T) :
    f x - f T = ∫ t in x..T,
      -iteratedDerivWithin 1 f (Icc x T) t := by
  have hsubset : Icc x T ⊆ Set.Ici 0 :=
    Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hx)
  have hcm_Icc : ContDiffOn ℝ (↑(0 + 1) : WithTop ℕ∞) f (Icc x T) :=
    (hcm.1.mono hsubset).of_le le_top
  have htaylor := taylor_integral_remainder hxT hcm_Icc
  -- Degree-0 Taylor polynomial: taylorWithinEval f 0 s x T = f x
  have h0 : taylorWithinEval f 0 (Icc x T) x T = f x := by
    simp [taylorWithinEval, taylorWithin, PolynomialModule.eval_single,
      taylorCoeffWithin]
  simp only [zero_add, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_mul, pow_zero, h0] at htaylor
  -- htaylor : f T - f x = ∫ iteratedDerivWithin 1 f (Icc x T) t dt
  rw [intervalIntegral.integral_neg]
  linarith

/-- The integral of `-f'` on `[0, T]` equals `f(0) - f(T)` and is bounded by `f(0)`. -/
lemma IsCompletelyMonotone.integral_mass (hcm : IsCompletelyMonotone f)
    (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T,
      -iteratedDerivWithin 1 f (Icc 0 T) t = f 0 - f T := by
  linarith [IsCompletelyMonotone.integral_neg_deriv hcm 0 T le_rfl hT]

/-! ## Measure construction for Bernstein -/

/-- The density `ρ_n(t) = (-1)^n/(n-1)! · t^{n-1} · f^{(n)}(t)` for the n-th
approximating measure in the Bernstein proof (Chafaï 2013). -/
def cm_density (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
    t ^ (n - 1) * iteratedDerivWithin n f (Set.Ici 0) t

/-- The n-th approximating measure σ_n for the Bernstein proof, with density
`ρ_n` on `(0, ∞)`. -/
def cm_measure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (cm_density f n t))

/-- The density `ρ_n` is nonneg for CM functions (product of nonneg factors). -/
lemma cm_density_nonneg (hcm : IsCompletelyMonotone f) (n : ℕ)
    (t : ℝ) (ht : 0 < t) : 0 ≤ cm_density f n t := by
  simp only [cm_density]
  split_ifs with hn
  · exact le_refl 0
  · have hcm_sign := hcm.2 n t (le_of_lt ht)
    have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
          iteratedDerivWithin n f (Set.Ici 0) t
        = t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Set.Ici 0) t) := by
          field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg (le_of_lt ht) _)
          (le_of_lt hfact_pos)) hcm_sign

/-- For `n = 1`, the density simplifies to `-f'(t)`. -/
lemma cm_density_one (t : ℝ) :
    cm_density f 1 t = -iteratedDerivWithin 1 f (Set.Ici 0) t := by
  simp [cm_density]

/-- The interval integral of `-f'` with the T-dependent set `Icc 0 T` equals the
integral with the fixed set `Ici 0` (both agree a.e. by set transfer at interior points). -/
lemma IsCompletelyMonotone.integral_neg_deriv_Ici
    (hcm : IsCompletelyMonotone f) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t =
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Set.Ici 0) t := by
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all volume
  intro t ht
  rw [uIoc_of_le (le_of_lt hT)] at ht
  have ht_pos : 0 < t := ht.1
  have hcda : ContDiffAt ℝ (↑1 : WithTop ℕ∞) f t :=
    (hcm.1.of_le le_top).contDiffAt (Ici_mem_nhds ht_pos)
  simp only [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT) hcda
      (Ioc_subset_Icc_self ht),
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
      (Set.mem_Ici.mpr (le_of_lt ht_pos))]

/-- The total mass `∫₀ᵀ (-f') dt → f(0) - L` as `T → ∞`, where `L = lim f(t)`.
This is the key uniform bound for the tightness argument in Bernstein's theorem. -/
lemma IsCompletelyMonotone.tendsto_total_mass
    (hcm : IsCompletelyMonotone f) {L : ℝ}
    (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto (fun T => ∫ t in (0 : ℝ)..T,
      -iteratedDerivWithin 1 f (Icc 0 T) t) Filter.atTop
        (nhds (f 0 - L)) :=
  Filter.Tendsto.congr' (Filter.EventuallyEq.symm
    ((Filter.eventually_gt_atTop 0).mono fun T hT =>
      IsCompletelyMonotone.integral_mass hcm T hT))
    (Filter.Tendsto.sub tendsto_const_nhds hL)

set_option maxHeartbeats 800000 in
/-- `-f'` is integrable on `(0, ∞)` for CM functions (total mass = `f(0) - L`).
Uses `integrableOn_Ioi_of_intervalIntegral_norm_tendsto` with the norm bound
from `tendsto_total_mass`. Extra heartbeats for ae norm computation. -/
lemma IsCompletelyMonotone.neg_deriv_integrableOn
    (hcm : IsCompletelyMonotone f) {L : ℝ}
    (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    IntegrableOn (fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t)
      (Set.Ioi 0) := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto (f 0 - L) 0
      (l := Filter.atTop) (b := id)
  · -- IntegrableOn on each Ioc 0 T (continuous on Ici 0 → integrable on compact Icc)
    intro T
    exact ((hcm.1.continuousOn_iteratedDerivWithin le_top
      (uniqueDiffOn_Ici 0)).neg.mono Icc_subset_Ici_self).integrableOn_compact
        isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · exact Filter.tendsto_id
  · -- ∫ ‖g‖ → f(0) - L: since g ≥ 0 by CM, ‖g‖ = g, so ∫ ‖g‖ = f(0) - f(T)
    have hnorm : ∀ᶠ T in Filter.atTop, (∫ t in (0 : ℝ)..id T,
        ‖(fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t) t‖) =
        f 0 - f T := by
      filter_upwards [Filter.eventually_gt_atTop 0] with T hT
      simp only [id]
      have : (∫ t in (0 : ℝ)..T,
          ‖(fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t) t‖) =
          ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Set.Ici 0) t :=
        intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
          rw [uIoc_of_le (le_of_lt hT)] at ht
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by linarith [hcm.deriv_nonpos t (le_of_lt ht.1)])])
      rw [this, ← IsCompletelyMonotone.integral_neg_deriv_Ici hcm T hT,
          IsCompletelyMonotone.integral_mass hcm T hT]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hnorm)
      (Filter.Tendsto.sub tendsto_const_nhds hL)

/-- The improper integral `∫₀^∞ (-f') dt = f(0) - L` for CM functions. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_deriv
    (hcm : IsCompletelyMonotone f) {L : ℝ}
    (hL : Filter.Tendsto f Filter.atTop (nhds L))
    (hint : IntegrableOn (fun t => -iteratedDerivWithin 1 f (Set.Ici 0) t)
      (Set.Ioi 0)) :
    ∫ t in Set.Ioi 0, -iteratedDerivWithin 1 f (Set.Ici 0) t =
      f 0 - L := by
  have htend := intervalIntegral_tendsto_integral_Ioi 0 hint Filter.tendsto_id
  have htend2 : Filter.Tendsto (fun T => ∫ t in (0 : ℝ)..T,
      -iteratedDerivWithin 1 f (Set.Ici 0) t) Filter.atTop
        (nhds (f 0 - L)) :=
    Filter.Tendsto.congr'
      ((Filter.eventually_gt_atTop 0).mono fun T hT =>
        ((IsCompletelyMonotone.integral_neg_deriv_Ici hcm T hT).symm.trans
          (IsCompletelyMonotone.integral_mass hcm T hT)).symm)
      (Filter.Tendsto.sub tendsto_const_nhds hL)
  exact tendsto_nhds_unique htend htend2

/-- **Packaging step**: if `f(x) = L + ∫ e^{-xp} dμ₀` with `μ₀` supported on `[0,∞)`,
then `μ = μ₀ + L·δ₀` gives `f(x) = ∫ e^{-xp} dμ` with `μ` finite and supported on `[0,∞)`. -/
lemma bernstein_packaging {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    {μ₀ : Measure ℝ} [IsFiniteMeasure μ₀] (hsupp₀ : μ₀ (Set.Iio 0) = 0)
    (hrep : ∀ t, 0 ≤ t → f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧ μ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  set μ := μ₀ + (ENNReal.ofReal L) • Measure.dirac (0 : ℝ)
  haveI : IsFiniteMeasure μ := by
    constructor
    simp only [μ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, mul_one]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.ofReal_lt_top⟩
  refine ⟨μ, inferInstance, ?_, ?_⟩
  · simp only [μ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator, Set.mem_Iio, lt_irrefl,
      ↓reduceIte, mul_zero, hsupp₀, add_zero]
  · intro t ht
    rw [hrep t ht]
    -- ∫ e^{-tp} d(μ₀ + L·δ₀) = ∫ e^{-tp} dμ₀ + L
    set ν := (ENNReal.ofReal L) • Measure.dirac (0 : ℝ)
    -- Use let to avoid ∂(c • μ) parsing ambiguity
    let ν := (ENNReal.ofReal L) • Measure.dirac (0 : ℝ)
    -- e^{-tp} is integrable: bounded by 1 on support [0,∞) of finite measure
    have exp_int : ∀ (μ' : Measure ℝ) [IsFiniteMeasure μ'],
        μ' (Set.Iio 0) = 0 →
        Integrable (fun p => Real.exp (-(t * p))) μ' := by
      intro μ' _ hsupp'
      apply Integrable.mono' (integrable_const (1 : ℝ))
      · fun_prop
      · rw [ae_iff]; refine measure_mono_null (fun p hp => ?_) hsupp'
        simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hp
        rw [Set.mem_Iio]; by_contra hge; push_neg at hge
        linarith [abs_of_nonneg (Real.exp_pos (-(t * p))).le,
          Real.exp_le_exp_of_le (neg_nonpos.mpr (mul_nonneg ht hge)),
          Real.exp_zero]
    have h1 : Integrable (fun p => Real.exp (-(t * p))) μ₀ :=
      exp_int μ₀ hsupp₀
    have h2 : Integrable (fun p => Real.exp (-(t * p))) ν := by
      haveI : IsFiniteMeasure ν := by
        constructor; simp only [ν, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, mul_one]
        exact ENNReal.ofReal_lt_top
      apply exp_int; simp [ν, Measure.smul_apply, Measure.dirac_apply,
        Set.indicator, Set.mem_Iio, lt_irrefl]
    show L + ∫ p, Real.exp (-(t * p)) ∂μ₀ = ∫ p, Real.exp (-(t * p)) ∂(μ₀ + ν)
    rw [integral_add_measure h1 h2]
    suffices h : ∫ p, Real.exp (-(t * p)) ∂ν = L by linarith
    rw [@integral_smul_measure ℝ ℝ _ _ _ (Measure.dirac 0)
      (fun p => Real.exp (-(t * p))) (ENNReal.ofReal L),
      integral_dirac, ENNReal.toReal_ofReal hL,
      mul_zero, neg_zero, Real.exp_zero, smul_eq_mul, mul_one]

/-! ## Rescaled measures and Prokhorov extraction -/

/-- The Bernstein kernel: `φ_n(x,p) = max(1 - xp/(n-1), 0)^{n-1}` for `n ≥ 2`.
After the change of variable `p = (n-1)/t`, the Taylor integral kernel on `[0, T]`
becomes `φ_n(x, p) = max(1 - xp/(n-1), 0)^{n-1}`, which converges pointwise
to `e^{-xp}` as `n → ∞` (the classical `(1-x/n)^n → e^{-x}` limit). -/
def bernstein_kernel (n : ℕ) (x p : ℝ) : ℝ :=
  if n ≤ 1 then 0
  else (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1)

/-- **Pointwise convergence of the Bernstein kernel** to the Laplace kernel:
`φ_n(x,p) → e^{-xp}` as `n → ∞`, for `x, p ≥ 0`.

Proof: For large `n`, `1 - xp/(n-1) > 0`, so the `max` is inactive and the kernel
equals `(1 + (-xp)/(n-1))^{n-1}`. This converges to `e^{-xp}` by
`Real.tendsto_one_add_div_pow_exp` (the Mathlib proof of `(1+t/n)^n → eᵗ`). -/
lemma bernstein_kernel_tendsto (x p : ℝ) (_hx : 0 ≤ x) (_hp : 0 ≤ p) :
    Tendsto (fun n : ℕ => bernstein_kernel n x p)
      atTop (nhds (Real.exp (-(x * p)))) := by
  set g := fun n : ℕ => (1 + (-(x * p)) / (↑n : ℝ)) ^ n with hg_def
  have hg_tendsto : Tendsto g atTop (nhds (Real.exp (-(x * p)))) :=
    Real.tendsto_one_add_div_pow_exp (-(x * p))
  have hshift : Tendsto (fun n : ℕ => g (n - 1)) atTop (nhds (Real.exp (-(x * p)))) :=
    hg_tendsto.comp (tendsto_atTop_atTop.mpr (fun b => ⟨b + 1, fun n hn => by omega⟩))
  apply Tendsto.congr' _ hshift
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨{n : ℕ | n ≥ Nat.ceil (x * p) + 2}, mem_atTop _, ?_⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [bernstein_kernel, hg_def]
  have hn1 : ¬(n ≤ 1) := by omega
  simp only [hn1, ite_false]
  have hn1_pos : (0 : ℝ) < ↑(n - 1) := Nat.cast_pos.mpr (by omega)
  have hn1_ge : x * p ≤ ↑(n - 1) := by
    calc x * p ≤ ↑(Nat.ceil (x * p)) := Nat.le_ceil _
    _ ≤ ↑(n - 1) := by exact_mod_cast (by omega : Nat.ceil (x * p) ≤ n - 1)
  congr 1
  rw [max_eq_left]
  · ring
  · rw [sub_nonneg]; exact div_le_one_of_le₀ hn1_ge hn1_pos.le

/-- The rescaled measure σ̃_n: pushforward of `cm_measure f n` under the map
`t ↦ (n-1)/t`, which sends `(0, ∞)` to `(0, ∞)`. After this change of
variable, the Taylor integral kernel becomes `(1 - xp/(n-1))_+^{n-1}`,
which converges pointwise to `e^{-xp}` as `n → ∞`. -/
def cm_rescaled (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  Measure.map (fun t => ((n : ℝ) - 1) / t) (cm_measure f n)

/-- The rescaling map `t ↦ (n-1)/t` is measurable. -/
lemma cm_rescaling_measurable (n : ℕ) :
    Measurable (fun t : ℝ => ((n : ℝ) - 1) / t) :=
  measurable_const.div measurable_id

/-- `cm_measure f n` lives on `(0, ∞)`: its complement has zero mass. -/
lemma cm_measure_compl_Ioi (f : ℝ → ℝ) (n : ℕ) :
    (cm_measure f n) (Set.Ioi 0)ᶜ = 0 := by
  unfold cm_measure
  rw [withDensity_apply _ (measurableSet_Ioi.compl)]
  apply setLIntegral_measure_zero
  rw [Measure.restrict_apply (measurableSet_Ioi.compl)]
  have : (Set.Ioi (0 : ℝ))ᶜ ∩ Set.Ioi 0 = ∅ := by
    ext x; simp [Set.mem_Ioi]
  rw [this, measure_empty]

/-- The rescaled measure σ̃_n is supported on `[0, ∞)` for `n ≥ 2`:
`t ↦ (n-1)/t` maps `(0, ∞)` into `(0, ∞)` when `n ≥ 2`. -/
lemma cm_rescaled_Iio_zero (f : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (cm_rescaled f n) (Set.Iio 0) = 0 := by
  unfold cm_rescaled
  rw [Measure.map_apply (cm_rescaling_measurable n) measurableSet_Iio]
  have h_sub :
      (fun t : ℝ => ((n : ℝ) - 1) / t) ⁻¹' Set.Iio 0 ⊆ (Set.Ioi 0)ᶜ := by
    intro t ht
    simp only [Set.mem_preimage, Set.mem_Iio] at ht
    simp only [Set.mem_compl_iff, Set.mem_Ioi, not_lt]
    by_contra h; push_neg at h
    have : (0 : ℝ) < (↑n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
      linarith
    linarith [div_pos this h]
  exact le_antisymm
    (le_trans (measure_mono h_sub) (le_of_eq (cm_measure_compl_Ioi f n)))
    (zero_le _)

/-- Pushforward preserves total mass. -/
lemma cm_rescaled_mass_eq (f : ℝ → ℝ) (n : ℕ) :
    (cm_rescaled f n) Set.univ = (cm_measure f n) Set.univ := by
  unfold cm_rescaled
  rw [Measure.map_apply (cm_rescaling_measurable n) MeasurableSet.univ,
    Set.preimage_univ]

set_option maxHeartbeats 3200000 in
/-- **IBP identity** for the CM density:
`∫₀ᵀ ρ_{m+2}(t) dt = B_{m+2}(T) + ∫₀ᵀ ρ_{m+1}(t) dt`
where `B_{m+2}(T) = (-1)^{m+2} T^{m+1}/(m+1)! · f^{(m+1)}(T)`.

The proof uses the FTC on the product `F(t) = t^{m+1} · c · f^{(m+1)}(t)` where
`c = (-1)^{m+2}/(m+1)!`. The derivative `F'` decomposes as
`cm_density f (m+2) - cm_density f (m+1)` by the factorial identity
`(m+1)·(-1)^{m+2}/(m+1)! = -(-1)^{m+1}/m!`. -/
private lemma cm_density_ibp_identity (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (m : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, cm_density f (m + 2) t =
    (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      iteratedDerivWithin (m + 1) f (Set.Ici 0) T +
    ∫ t in (0 : ℝ)..T, cm_density f (m + 1) t := by
  set g := iteratedDerivWithin (m + 1) f (Set.Ici 0)
  set g' := iteratedDerivWithin (m + 2) f (Set.Ici 0)
  set c : ℝ := (-1) ^ (m + 2) / ↑(m + 1).factorial
  set F := fun t : ℝ => t ^ (m + 1) * (c * g t)
  have hg_cont : ContinuousOn g (Set.Ici 0) :=
    hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0)
  have hg_deriv : ∀ t, 0 < t → HasDerivAt g (g' t) t := by
    intro t ht
    have hmem : Set.Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds ht
    have hda := (hcm.1.differentiableOn_iteratedDerivWithin
      (show (↑(m + 1) : WithTop ℕ∞) < ⊤ from WithTop.coe_lt_top _)
      (uniqueDiffOn_Ici 0)).hasDerivAt hmem
    show HasDerivAt g (g' t) t; convert hda using 1; show g' t = deriv g t
    simp only [g, g']
    rw [show m + 2 = (m + 1) + 1 from by omega, iteratedDerivWithin_succ,
      derivWithin_of_mem_nhds hmem]
  have huIcc : Set.uIcc (0 : ℝ) T = Set.Icc 0 T := Set.uIcc_of_le (le_of_lt hT)
  have hF_cont : ContinuousOn F (Set.Icc 0 T) :=
    ((continuous_pow _).continuousOn).mul
      (continuousOn_const.mul (hg_cont.mono Set.Icc_subset_Ici_self))
  have hF_deriv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt F
      (↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t)) t :=
    fun t ht => (hasDerivAt_pow (m + 1) t).mul ((hg_deriv t ht.1).const_mul c)
  have hcm_int : ∀ k, k ≠ 0 → IntervalIntegrable (fun t => cm_density f k t)
      MeasureTheory.volume 0 T := by
    intro k hk; apply ContinuousOn.intervalIntegrable; rw [huIcc]
    apply ContinuousOn.mono _ Set.Icc_subset_Ici_self
    change ContinuousOn (fun t => cm_density f k t) (Set.Ici 0)
    have : (fun t => cm_density f k t) = fun t =>
        (-1 : ℝ) ^ k / ↑(k - 1).factorial * t ^ (k - 1) *
          iteratedDerivWithin k f (Set.Ici 0) t := funext fun t => by
      simp [cm_density, hk]
    rw [this]
    exact (continuousOn_const.mul (continuous_pow _).continuousOn).mul
      (hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0))
  have hF'_eq : ∀ t, ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t) =
      cm_density f (m + 2) t - cm_density f (m + 1) t := by
    intro t
    simp only [cm_density, show m + 2 ≠ 0 from by omega, show m + 1 ≠ 0 from by omega,
      ite_false, show m + 2 - 1 = m + 1 from by omega,
      show m + 1 - 1 = m from by omega, g, g', c]
    have : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * ↑m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]
    have : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have : ((m : ℝ) + 1) ≠ 0 := by positivity
    have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
    rw [this]; field_simp; ring
  have hF'_int : IntervalIntegrable
      (fun t => ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t))
      MeasureTheory.volume 0 T :=
    ((hcm_int _ (by omega)).sub (hcm_int _ (by omega))).congr
      fun t _ => (hF'_eq t).symm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (le_of_lt hT) hF_cont hF_deriv hF'_int
  have hstep1 : ∫ t in (0 : ℝ)..T,
      (cm_density f (m + 2) t - cm_density f (m + 1) t) = F T - F 0 := by
    rw [← hftc]
    exact intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun t _ => (hF'_eq t).symm)
  have hF0 : F 0 = 0 := by simp [F, zero_pow (show m + 1 ≠ 0 from by omega)]
  rw [hF0, sub_zero] at hstep1
  rw [intervalIntegral.integral_sub (hcm_int _ (by omega))
    (hcm_int _ (by omega))] at hstep1
  suffices hgoal : (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      g T = F T by linarith
  simp only [F, c]; ring

set_option maxHeartbeats 3200000 in
-- IBP step: boundary term ≤ 0 by CM sign condition
private lemma cm_density_ibp_step (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 2 ≤ k) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, cm_density f k t ≤
    ∫ t in (0 : ℝ)..T, cm_density f (k - 1) t := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 from by omega]
  have hibp := cm_density_ibp_identity f hcm m T hT
  set B := (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
    iteratedDerivWithin (m + 1) f (Set.Ici 0) T
  have hB : B ≤ 0 := by
    have h_neg : (-1 : ℝ) ^ (m + 2) *
        iteratedDerivWithin (m + 1) f (Set.Ici 0) T ≤ 0 := by
      have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) :=
        pow_succ (-1) (m + 1)
      rw [this]; nlinarith [hcm.2 (m + 1) T (le_of_lt hT)]
    suffices B = T ^ (m + 1) / ↑(m + 1).factorial *
        ((-1 : ℝ) ^ (m + 2) *
          iteratedDerivWithin (m + 1) f (Set.Ici 0) T) by
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (pow_nonneg (le_of_lt hT) _) (Nat.cast_nonneg _)) h_neg
    simp only [B]; ring
  linarith

/-- **Total mass bound**: `cm_measure f n` is a finite measure with total mass
`≤ f(0) - L` for CM functions with `f(t) → L`.

By IBP recursion, `∫₀ᵀ ρ_k = B_k(T) + ∫₀ᵀ ρ_{k-1}` where each boundary term
`B_k(T) = (-1)^k T^{k-1}/(k-1)! · f^{(k-1)}(T) ≤ 0` by the CM sign condition.
Iterating down to `k = 1`: `∫₀ᵀ ρ_n ≤ ∫₀ᵀ ρ_1 = f(0) - f(T) ≤ f(0) - L`. -/
lemma cm_measure_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 2 ≤ n) (L : ℝ)
    (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    IsFiniteMeasure (cm_measure f n) ∧
    (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L) := by
  have hn0 : n ≠ 0 := by omega
  -- cm_density is continuous on [0,∞)
  have hcont : ContinuousOn (cm_density f n) (Set.Ici 0) := by
    unfold cm_density; simp only [hn0, ↓reduceIte]
    exact ((continuousOn_const.mul
      ((continuousOn_pow _).mono fun _ _ => trivial)).mul
      (hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0)))
  -- IBP recursion: ∫_0^T ρ_n ≤ f(0) - f(T) ≤ f(0) - L
  -- (each IBP step adds a nonpositive boundary term by CM sign condition)
  have hbound : ∀ T, 0 < T →
      ∫ t in (0 : ℝ)..T, cm_density f n t ≤ f 0 - L := by
    -- Base case: ∫₀ᵀ ρ₁ = f(0) - f(T)
    have base : ∀ T, 0 < T →
        ∫ t in (0 : ℝ)..T, cm_density f 1 t = f 0 - f T := by
      intro T hT
      have h1 : ∫ t in (0 : ℝ)..T, cm_density f 1 t =
          ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Set.Ici 0) t :=
        intervalIntegral.integral_congr_ae
          (Filter.Eventually.of_forall fun t _ => cm_density_one t)
      rw [h1, ← hcm.integral_neg_deriv_Ici T hT, hcm.integral_mass T hT]
    -- Induction: for j ≥ 1, ∫₀ᵀ ρ_j ≤ f(0) - f(T)
    have density_le : ∀ j, 1 ≤ j → ∀ T, 0 < T →
        ∫ t in (0 : ℝ)..T, cm_density f j t ≤ f 0 - f T := by
      intro j hj
      induction j with
      | zero => omega
      | succ p ih =>
        intro T hT
        by_cases hp : p = 0
        · subst hp; exact le_of_eq (base T hT)
        · calc ∫ t in (0 : ℝ)..T, cm_density f (p + 1) t
              ≤ ∫ t in (0 : ℝ)..T, cm_density f p t := by
                simpa using cm_density_ibp_step f hcm (p + 1) (by omega) T hT
            _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp) T hT
    -- L ≤ f(T) for T > 0 (antitone + limit)
    intro T hT
    have hfT : L ≤ f T := by
      have htop : (⊤ : WithTop ℕ∞) ≠ 0 := Ne.symm (ne_of_beq_false rfl)
      set g₀ := fun t : ℝ => f (max t 0)
      have hg_anti : Antitone g₀ := fun a b hab =>
        (antitoneOn_of_deriv_nonpos (convex_Ici 0) hcm.1.continuousOn
          ((hcm.1.differentiableOn htop).mono interior_subset)
          (fun x hx => by
            rw [interior_Ici] at hx
            have h1 := hcm.deriv_nonpos x (le_of_lt hx)
            rwa [iteratedDerivWithin_one,
              derivWithin_of_mem_nhds (Ici_mem_nhds hx)] at h1))
          (Set.mem_Ici.mpr (le_max_right _ _))
          (Set.mem_Ici.mpr (le_max_right _ _))
          (max_le_max_right 0 hab)
      have := hg_anti.le_of_tendsto
        (hL.congr' (Filter.eventually_atTop.mpr
          ⟨0, fun t ht => by simp [g₀, max_eq_left ht]⟩)) T
      simp only [g₀, max_eq_left (le_of_lt hT)] at this
      exact this
    linarith [density_le n (by omega : 1 ≤ n) T hT]
  -- cm_density integrable on (0,∞) from bounded interval integrals
  have hint : IntegrableOn (cm_density f n) (Set.Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
      (l := Filter.atTop) (b := id)
    · intro T
      exact (hcont.mono Set.Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
        |>.mono_set Set.Ioc_subset_Icc_self
    · exact Filter.tendsto_id
    · filter_upwards [Filter.eventually_gt_atTop 0] with T hT; simp only [id]
      calc ∫ t in (0 : ℝ)..T, ‖cm_density f n t‖
          = ∫ t in (0 : ℝ)..T, cm_density f n t := by
            apply intervalIntegral.integral_congr_ae; apply ae_of_all
            intro t ht; rw [uIoc_of_le (le_of_lt hT)] at ht
            rw [Real.norm_eq_abs, abs_of_nonneg (cm_density_nonneg hcm n t ht.1)]
        _ ≤ f 0 - L := hbound T hT
  -- IsFiniteMeasure from integrability
  have hfin : IsFiniteMeasure (cm_measure f n) := by
    unfold cm_measure
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  -- Mass bound: lintegral = ofReal(integral) ≤ ofReal(f(0) - L)
  have hmass : (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L) := by
    change (volume.restrict (Set.Ioi 0)).withDensity
      (fun t => ENNReal.ofReal (cm_density f n t)) Set.univ ≤ _
    rw [withDensity_apply _ MeasurableSet.univ]; simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
        cm_density_nonneg hcm n t ht)]
    exact ENNReal.ofReal_le_ofReal
      (le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint
        Filter.tendsto_id) (Filter.eventually_atTop.mpr
          ⟨1, fun T hT => hbound T (by linarith)⟩))
  exact ⟨hfin, hmass⟩

/-! ### Prokhorov extraction + Laplace representation -/

/-- The rescaled measure `cm_rescaled f n` is a finite measure when the
underlying `cm_measure f n` is finite. -/
private lemma cm_rescaled_isFiniteMeasure (f : ℝ → ℝ) (n : ℕ)
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
    exact (hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0)).mono
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
      (show (↑k : WithTop ℕ∞) < ⊤ from WithTop.coe_lt_top _)
      (uniqueDiffOn_Ici 0)).hasDerivAt hmem using 1
    simp only [g', iteratedDerivWithin_succ, derivWithin_of_mem_nhds hmem]
  have hu'_int : IntervalIntegrable u' volume x T :=
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _))).intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume x T := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le (le_of_lt hxT)]
    exact (hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0)).mono
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
      change u' t * g t = _; rw [hu'_eq])
  linarith

/-- Boundary decay: `(-1)^{k+1}/k! (T-x)^k D^k f(T) → 0` as `T → ∞` for CM functions.
This follows from the integrability of the k-th CM density on `(0, ∞)`. -/
private lemma boundary_term_decay (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto (fun T => (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Set.Ici 0) T) Filter.atTop (nhds 0) := by
  set h := fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T
  -- h ≥ 0 antitone, t^{k-1}h(t) integrable ⟹ T^k h(T) → 0 via
  -- T^k h(T) ≤ 2^k ∫_{T/2}^T s^{k-1} h(s) ds → 0
  have hkey : Tendsto (fun T => (T - x) ^ k * h T) atTop (nhds 0) := by
    -- h ≥ 0 antitone on [0,∞), cm_density f k = t^{k-1}h(t)/(k-1)! integrable on (0,∞)
    -- Squeeze: 0 ≤ (T-x)^k h(T) ≤ T^k h(T) = 2^k(T/2)^k h(T)
    -- For antitone h: (T/2)^{k-1} h(T) ≤ t^{k-1} h(t) on [T/2,T]
    -- So (T/2)^k h(T) ≤ ∫_{T/2}^T t^{k-1} h(t) dt = (k-1)! ∫_{T/2}^T cm_density
    -- ≤ (k-1)! ∫_{Ioi(T/2)} cm_density → 0 (tail of integrable function)
    sorry
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
      (hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0)))
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
        ((hcm.1.differentiableOn (Ne.symm (ne_of_beq_false rfl))).mono interior_subset)
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
      ((hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0)).mono
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
          (hcm.1.of_le le_top).contDiffAt (Ici_mem_nhds ht_pos)
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

private lemma chafai_identity (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
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
        (hcm.1.continuousOn_iteratedDerivWithin le_top (uniqueDiffOn_Ici 0)))
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

private lemma finite_measure_subseq_limit
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
  -- Step 1: Define ν_n = σ_n + δ_{-1}, π_n = normalize(ν_n)
  haveI hν_fin : ∀ n, IsFiniteMeasure (σ n + Measure.dirac (-1 : ℝ)) := fun n => by
    haveI := hfin n; constructor
    simp only [Measure.add_apply, Measure.dirac_apply, Set.indicator_univ, Pi.one_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.one_lt_top⟩
  set ν : ℕ → FiniteMeasure ℝ := fun n => ⟨σ n + Measure.dirac (-1 : ℝ), hν_fin n⟩
  set π : ℕ → ProbabilityMeasure ℝ := fun n => (ν n).normalize
  -- Step 2: Show {↑π_n} is tight (from htight + hsupp + normalize_le)
  have hν_ne : ∀ n, ν n ≠ 0 := fun n => by
    intro h; have := congr_arg (· Set.univ) (congr_arg FiniteMeasure.toMeasure h)
    simp only [ν, FiniteMeasure.toMeasure_mk, Measure.add_apply, Measure.dirac_apply,
      Set.indicator_univ, Pi.one_apply, FiniteMeasure.toMeasure_zero,
      Measure.coe_zero, Pi.zero_apply] at this
    exact absurd this (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_left le_rfl)))
  have hν_mass : ∀ n, 1 ≤ (ν n).mass := fun n => by
    change 1 ≤ ((↑(ν n) : Measure ℝ) Set.univ).toNNReal
    simp only [ν, FiniteMeasure.toMeasure_mk, Measure.add_apply, Measure.dirac_apply,
      Set.indicator_univ, Pi.one_apply]
    rw [show (1 : NNReal) = (1 : ENNReal).toNNReal from by simp,
      ENNReal.toNNReal_le_toNNReal ENNReal.one_ne_top
        (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.one_lt_top⟩).ne]
    exact le_add_left le_rfl
  have htight_π : IsTightMeasureSet {μ : Measure ℝ | ∃ n, ↑(π n) = μ} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hε_top : ε = ⊤
    · exact ⟨∅, isCompact_empty, fun μ ⟨n, hμ⟩ => by subst hμ; simp [hε_top]⟩
    obtain ⟨R, hR⟩ := htight ε.toReal (ENNReal.toReal_pos (ne_of_gt hε) hε_top)
    refine ⟨Set.Icc (-1) (max R 0), isCompact_Icc, fun μ ⟨n, hμ⟩ => ?_⟩
    subst hμ
    -- ↑(π n)(K^c) ≤ ↑(ν n)(K^c) ≤ σ_n(Ioi R) ≤ ε
    calc (↑(π n) : Measure ℝ) (Set.Icc (-1) (max R 0))ᶜ
        = (↑((ν n).normalize) : Measure ℝ) _ := by rw [show π n = (ν n).normalize from rfl]
      _ ≤ (↑(ν n) : Measure ℝ) _ := normalize_le _ (hν_ne n) (hν_mass n) _
      _ ≤ ENNReal.ofReal ε.toReal := by
          -- ↑(ν n)(K^c) = (σ_n + δ_{-1})(K^c) ≤ σ_n(Ioi R) ≤ ε
          show (σ n + Measure.dirac (-1 : ℝ)) (Set.Icc (-1) (max R 0))ᶜ ≤ _
          have h_iio : σ n (Set.Iio (-1)) = 0 :=
            le_antisymm (le_trans (measure_mono (Set.Iio_subset_Iio (by norm_num : (-1:ℝ) ≤ 0)))
              (le_of_eq (hsupp n))) (zero_le _)
          have hd : Measure.dirac (-1 : ℝ) (Set.Icc (-1) (max R 0))ᶜ = 0 := by
            rw [Measure.dirac_apply]
            simp [Set.indicator, show (-1:ℝ) ∈ Set.Icc (-1) (max R 0) from
              ⟨le_refl _, by linarith [le_max_right R 0]⟩]
          simp only [Measure.add_apply, hd, add_zero]
          calc σ n (Set.Icc (-1) (max R 0))ᶜ
              ≤ σ n (Set.Iio (-1)) + σ n (Set.Ioi (max R 0)) :=
                le_trans (measure_mono (fun t => by
                  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le,
                    Set.mem_union, Set.mem_Iio, Set.mem_Ioi]; tauto))
                  (measure_union_le _ _)
            _ = σ n (Set.Ioi (max R 0)) := by rw [h_iio, zero_add]
            _ ≤ σ n (Set.Ioi R) :=
                measure_mono (Set.Ioi_subset_Ioi (le_max_left _ _))
            _ ≤ _ := hR n
      _ = ε := ENNReal.ofReal_toReal hε_top
  -- Step 3: Prokhorov → compact → seq compact → subseq
  have htight' : IsTightMeasureSet {μ : Measure ℝ | ∃ p ∈ range π, ↑p = μ} := by
    convert htight_π using 1; ext μ; simp [eq_comm]
  have hcpt := isCompact_closure_of_isTightMeasureSet htight'
  obtain ⟨π₀, _, φ, hφ, hπ_tend⟩ :=
    (isCompact_iff_isSeqCompact.mp hcpt).subseq_of_frequently_in
      ((frequently_atTop.mpr fun n =>
        ⟨n, le_refl n, subset_closure (mem_range.mpr ⟨n, rfl⟩)⟩))
  -- Step 4: Recover σ convergence from π convergence via mass rescaling.
  -- Key idea: ∫ g dσ_{φ(k)} = ∫ g dν_{φ(k)} - g(-1)
  --   = mass(ν_{φ(k)}) · ∫ g dπ_{φ(k)} - g(-1).
  -- Mass convergence: mass(ν_{φ(k)}) ∈ [1, C+1] bounded, so by
  -- Bolzano-Weierstrass extract sub-subsequence ψ with mass(ν_{φ(ψ(k))}) → m₀.
  -- Then ∫ g dσ_{φ(ψ(k))} → m₀ · ∫ g dπ₀ - g(-1) =: ∫ g dμ₀.
  -- Define μ₀ via Riesz: ∫ g dμ₀ = m₀ · ∫ g dπ₀ - g(-1).
  -- Alternatively, use FiniteMeasure.tendsto_normalize_iff_tendsto
  -- to convert π convergence → ν convergence (as FiniteMeasure), then
  -- subtract δ_{-1} to recover σ convergence.
  -- Properties: μ₀(Iio 0) = 0 from Portmanteau (Iio 0 open, supp on [0,∞)),
  -- μ₀(univ) ≤ C from mass bound, IsFiniteMeasure from mass bound.
  sorry

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

/-- Weak convergence of `e^{-xp}` integrals for measures supported on `[0,∞)`,
via the bounded continuous surrogate `exp_bcf`. -/
private lemma tendsto_exp_integral
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
    intro n p; simp [bernstein_kernel]; split_ifs <;> positivity
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
        apply Real.exp_le_exp_of_le; linarith [mul_le_mul_of_nonneg_left (le_of_lt hpR) (le_of_lt hx)]
    linarith [hkernel_nn n p]

-- **Kernel approximation error → 0**: For measures `σ_n` supported on `[0,∞)`
-- with uniformly bounded mass, the integral of the difference
-- `φ_{n+2}(x,·) - e^{-x·}` against `σ_n` tends to zero.
--
-- For `x = 0` the integrand is identically 0. For `x > 0`, the convergence
-- `φ_n(x,p) → e^{-xp}` is UNIFORM in `p ∈ [0,∞)` (both functions have exponential
-- tail decay), so `|∫(φ_n - e^{-xp})dσ_n| ≤ sup|φ_n - e^{-xp}| · σ_n(ℝ) → 0`.
set_option maxHeartbeats 3200000 in
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

private lemma prokhorov_limit_identification (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) (hL_nn : 0 ≤ L)
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
    -- From hidentity: f(x) - L = ∫ kernel dσ_n and kernel ≤ exp(-xp):
    -- For p ≥ K: 1 - kernel(n,x₀,p) ≥ 1 - exp(-x₀K) (using kernel ≤ exp(-xp)).
    -- So (1-exp(-x₀K))·σ_n(Ioi K) ≤ ∫(1-kernel)dσ_n = σ_n(ℝ)-(f(x₀)-L) ≤ f(0)-f(x₀).
    -- Given ε > 0: choose x₀ > 0 with f(0)-f(x₀) < ε/2 (continuity at 0),
    -- then K with 1-exp(-x₀K) > 1/2. Result: σ_n(Ioi K) ≤ ε for all n.
    sorry
  obtain ⟨μ₀, φ, hfin_μ, hφ_mono, hsupp_μ, hmass_μ, hweak⟩ :=
    finite_measure_subseq_limit σ (f 0 - L) hfin_σ hmass_σ hsupp_σ htight_σ
  -- Step 2: Verify the Laplace identity via diagonal convergence
  refine ⟨μ₀, hfin_μ, hsupp_μ, fun t ht => ?_⟩
  -- We need: f t = L + ∫ e^{-tp} dμ₀, i.e., f t - L = ∫ e^{-tp} dμ₀
  have hdiag := diagonal_convergence (C := f 0 - L) f L
    σ φ μ₀ hfin_σ hφ_mono hweak hmass_σ hsupp_σ hsupp_μ t ht
    (fun n => hident_σ n (by omega) t ht)
  linarith

/-- **Prokhorov extraction + Laplace verification** (Chafaï 2013).

For each `n ≥ 2`, the pushforward `σ̃_n = cm_rescaled f n` has:
- Total mass `≤ f(0) - L` (from `cm_measure_finite_mass`)
- Support on `[0, ∞)` (from `cm_rescaled_Iio_zero`)

The correct Chafaï identity (for each fixed `n` and `x ≥ 0`):

  `f(x) - L = ∫ φ_n(xp) dσ̃_n(p)`

where `φ_n(u) = (1 - u/(n-1))_+^{n-1}`. This follows from the Taylor integral
remainder on `[x, T]` with `T → ∞`, using the boundary term decay
`T^k f^{(k)}(T) → 0` for CM functions (which follows from the integrability
of `(-1)^k f^{(k)}` on `[0, ∞)` and its monotonicity).

NOTE: An earlier decomposition incorrectly stated `∫ φ_n dσ̃_n = f(x) - taylorPoly(n-1, 0, x)`.
This is FALSE: the Bernstein integral is over `(x, ∞)` while the Taylor remainder is over
`(0, x)` — different domains with different kernels.

Given the correct identity, the proof concludes:
1. **Prokhorov** (`isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le`):
   extract `σ̃_{n_k} → μ₀` weakly.
2. **Diagonal convergence**: `∫ φ_{n_k} dσ̃_{n_k} → ∫ e^{-xp} dμ₀` using
   `bernstein_kernel_tendsto` + weak convergence + dominated convergence.
3. **Conclusion**: `f(x) - L = ∫ e^{-xp} dμ₀`. -/

lemma cm_prokhorov_and_verify (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L))
    (hL_nn : 0 ≤ L)
    (hmass : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_measure f n) ∧
      (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L))
    (hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Set.Iio 0) = 0) :
    ∃ (μ₀ : Measure ℝ), IsFiniteMeasure μ₀ ∧ μ₀ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t →
        f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  -- Step 1: cm_rescaled is finite for n ≥ 2
  have hfin_rescaled : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_rescaled f n) := by
    intro n hn; haveI := (hmass n hn).1
    exact cm_rescaled_isFiniteMeasure f n
  -- Step 2: mass bound for rescaled measures
  have hmass_rescaled : ∀ n, 2 ≤ n →
      (cm_rescaled f n) Set.univ ≤ ENNReal.ofReal (f 0 - L) := by
    intro n hn; rw [cm_rescaled_mass_eq]; exact (hmass n hn).2
  -- Step 3: Chafaï identity (proved in chafai_identity, sorry'd there)
  have hchafai : ∀ n, 2 ≤ n → ∀ x, 0 ≤ x →
      f x - L = ∫ p, bernstein_kernel n x p ∂(cm_rescaled f n) :=
    fun n hn x hx => chafai_identity f hcm n hn x hx L hL
  -- Step 4: Prokhorov extraction + limit identification
  exact prokhorov_limit_identification f hcm L hL hL_nn hmass_rescaled hsupp
    hfin_rescaled hchafai

/-- **CM Laplace representation** (Chafaï 2013 argument). For a CM function
`f` with limit `L ≥ 0` at infinity, there exists a finite positive measure
`μ₀` on `[0, ∞)` with `f(t) = L + ∫ e^{-tp} dμ₀(p)`.

The proof factors into sorry-free structural lemmas (support, mass
preservation) and two sorry'd analytic steps:
  1. `cm_measure_finite_mass` — total mass bound from Taylor's formula
  2. `cm_prokhorov_and_verify` — Prokhorov + limit identification

Mathlib tools for resolving the sorry's:
  - `isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le` (Prokhorov)
  - `IsCompact.isSeqCompact` (compact → sequentially compact)
  - `FiniteMeasure.tendsto_iff_forall_integral_tendsto` (weak convergence)
  - `taylor_integral_remainder` (proved above, sorry-free) -/
theorem cm_laplace_representation (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L)) (hL_nn : 0 ≤ L) :
    ∃ (μ₀ : Measure ℝ), IsFiniteMeasure μ₀ ∧ μ₀ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  have hmass : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_measure f n) ∧
      (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L) :=
    fun n hn => cm_measure_finite_mass f hcm n hn L hL
  have hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Set.Iio 0) = 0 :=
    fun n hn => cm_rescaled_Iio_zero f n hn
  exact cm_prokhorov_and_verify f hcm L hL hL_nn hmass hsupp

/-- **Bernstein's theorem** (1928). Every completely monotone function on `[0, ∞)` is
the Laplace transform of a finite positive measure on `[0, ∞)`.

Proof outline (Chafaï 2013), using `taylor_integral_remainder`:
1. Taylor integral remainder ⟹ `f(x) = boundary(n,T) + ∫_x^T ρ_n(t) dt` (nonneg)
2. Pushforward `p = (n-1)/t` ⟹ kernel `(1-xp/(n-1))^{n-1} → e^{-xp}`
3. Total variation `|σ̃_n| = f(0) - f(∞)` (uniform bound)
4. Prokhorov ⟹ `σ̃_{n_k} → μ` weakly
5. Portmanteau ⟹ `f(x) = ∫ e^{-xp} dμ(p)` -/
theorem bernstein_theorem (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      μ (Set.Iio 0) = 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  -- ═══════════════════════════════════════════════════════════════
  -- Established infrastructure (all sorry-free):
  -- ═══════════════════════════════════════════════════════════════
  -- Step 1: f has a limit L ≥ 0 at infinity
  obtain ⟨L, hL_tendsto, hL_nonneg⟩ := IsCompletelyMonotone.tendsto_atTop hcm
  -- Step 2: -f' is integrable on (0,∞) with total mass f(0) - L
  have hint := IsCompletelyMonotone.neg_deriv_integrableOn hcm hL_tendsto
  have hmass := IsCompletelyMonotone.integral_Ioi_neg_deriv hcm hL_tendsto hint
  -- Step 3: The density ρ_n is nonneg (cm_density_nonneg)
  -- Step 4: The Taylor remainder has definite sign (taylor_nonneg_remainder)
  -- Step 5: f(x) - f(T) = ∫ (-f') dt on each [x,T] (integral_neg_deriv)
  -- ═══════════════════════════════════════════════════════════════
  -- Step 6: Prokhorov + Portmanteau → μ₀ with f = L + ∫ e^{-xp} dμ₀
  -- ═══════════════════════════════════════════════════════════════
  have ⟨μ₀, hfin₀, hsupp₀, hrep⟩ :=
    cm_laplace_representation f hcm L hL_tendsto hL_nonneg
  -- Step 7: Package μ = μ₀ + L·δ₀ (sorry-free)
  exact @bernstein_packaging f L hL_nonneg μ₀ hfin₀ hsupp₀ hrep

end
