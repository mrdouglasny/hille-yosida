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
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

open MeasureTheory Set intervalIntegral

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

/-- **Total mass bound**: `cm_measure f n` is a finite measure with total mass
`≤ f(0) - L` for CM functions with `f(t) → L`.

By Taylor's formula with integral remainder at `x = 0`:
  `f(0) - f(T) = Σ_{k=1}^{n-1} (boundary terms at T) + ∫₀ᵀ ρ_n(t) dt`
where each boundary term `(-1)^k f^{(k)}(T) T^k / k!` is nonneg (CM sign)
and tends to 0 as `T → ∞` (since `f^{(k)}(T) → 0` for CM functions).
Taking `T → ∞`: `∫₀^∞ ρ_n(t) dt ≤ f(0) - L`. -/
lemma cm_measure_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 2 ≤ n) (L : ℝ)
    (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    IsFiniteMeasure (cm_measure f n) ∧
    (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L) := by
  exact sorry

/-- **Prokhorov extraction + representation verification** (combined).

Given:
  - σ̃_n = `cm_rescaled f n` supported on `[0, ∞)` with mass `≤ f(0) - L`

Produces: a finite measure `μ₀` on `[0, ∞)` with `f(t) = L + ∫ e^{-tp} dμ₀`.

**Step 1 — Tightness**: `σ̃_n([0,R]ᶜ) ≤ C/R` by Markov's inequality on the
first moment `∫ p dσ̃_n(p)`, which is uniformly bounded.

**Step 2 — Prokhorov**: The set
  `{μ : FiniteMeasure ℝ | μ.mass ≤ C ∧ ∀ k, μ(Icc(-k)(k))ᶜ ≤ u_k}`
is compact by `isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le`.
The σ̃_n lie in this set. Extract σ̃_{n_k} → μ₀ weakly via sequential
compactness (`IsCompact.isSeqCompact`).

**Step 3 — Representation**: For fixed `x ≥ 0`, the Taylor integral identity
gives `f(x) - L = lim_k ∫ φ_{n_k}(x,p) dσ̃_{n_k}(p)` where
`φ_n(x,p) = (1 - xp/(n-1))_+^{n-1}`. Since `φ_n → e^{-x·}` uniformly on
compacts with `|φ_n| ≤ 1`, the weak convergence
(`FiniteMeasure.tendsto_iff_forall_integral_tendsto`) + dominated convergence
gives `∫ e^{-xp} dμ₀(p) = f(x) - L`. -/
lemma cm_prokhorov_and_verify (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (L : ℝ) (hL : Filter.Tendsto f Filter.atTop (nhds L))
    (hL_nn : 0 ≤ L)
    (hmass : ∀ n, 2 ≤ n → IsFiniteMeasure (cm_measure f n) ∧
      (cm_measure f n) Set.univ ≤ ENNReal.ofReal (f 0 - L))
    (hsupp : ∀ n, 2 ≤ n → (cm_rescaled f n) (Set.Iio 0) = 0) :
    ∃ (μ₀ : Measure ℝ), IsFiniteMeasure μ₀ ∧ μ₀ (Set.Iio 0) = 0 ∧
      ∀ t, 0 ≤ t →
        f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀ := by
  exact sorry

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
