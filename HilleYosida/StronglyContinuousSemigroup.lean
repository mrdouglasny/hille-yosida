/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Strongly Continuous Semigroups and the Hille-Yosida Theorem

This file defines strongly continuous one-parameter semigroups (C₀-semigroups) on
Banach spaces, their infinitesimal generators, the resolvent operator via the
Laplace transform, and the forward direction of the Hille-Yosida theorem.

## Main Definitions

* `StronglyContinuousSemigroup` — a family `S(t)` of bounded linear operators
  for `t ≥ 0` satisfying `S(0) = Id`, `S(s+t) = S(s) ∘ S(t)`, and strong
  continuity at `t = 0` (Def. 1 in [Linares]).

* `ContractingSemigroup` — a C₀-semigroup of contractions: `‖S(t)‖ ≤ 1`
  for all `t ≥ 0` (Def. 3 in [Linares]). Corresponds to `M = 1, ω = 0`
  in the growth bound.

* `domain` — the generator domain `D(A) = {x : lim_{t→0⁺} (S(t)x - x)/t exists}`
  as a `Submodule ℝ X` (Def. 2 in [Linares]).

* `generatorMap` — the infinitesimal generator `A` as a `LinearMap` from the
  domain, `Ax = lim_{t→0⁺} (S(t)x - x)/t`.

* `ContractingSemigroup.resolvent` — the resolvent `R(λ)x = ∫₀^∞ e^{-λt} S(t)x dt`
  for contraction semigroups (eq. 0.13 in [Linares]), defined via
  `LinearMap.mkContinuous` with built-in bound `‖R(λ)‖ ≤ 1/λ`.

## Main Results

* `normBoundedOnUnitInterval` — `∃ M ≥ 1, ∀ t ∈ [0,1], ‖S(t)‖ ≤ M`, via
  the Banach-Steinhaus theorem (uniform boundedness principle).
* `existsGrowthBound` — every C₀-semigroup has exponential growth:
  `‖S(t)‖ ≤ M e^{ωt}` (Thm. 1 in [Linares], eq. 0.3).
* `strongContAt` — strong continuity at every `t₀ ≥ 0`, not just at 0
  (Cor. 1 in [Linares]).
* `hilleYosidaResolventBound` — `‖R(λ)‖ ≤ 1/λ` for contraction semigroups
  (eq. 0.14 in [Linares]; Thm. 6(ii), forward direction of Hille-Yosida).

## What is NOT yet proved

* `resolventMapsToDomain` — `R(λ)x ∈ D(A)`, proved via the integral shift
  trick (eq. 0.15 in [Linares]).
* `resolventRightInv` — `(λI - A)R(λ) = I` (eq. 0.16 in [Linares]).
* The converse (sufficiency) direction of Hille-Yosida, which requires the
  Yosida approximation `A_λ = λ A R_λ(A) = λ² R_λ(A) - λI` (eq. 0.19).

## References

* [EN] Engel-Nagel, "One-Parameter Semigroups for Linear Evolution Equations",
  Graduate Texts in Mathematics 194, Springer (2000). Primary reference.
  Ch. I §5: C₀-semigroups. Ch. II §1: Generators and resolvents.
  Ch. II §3: Hille-Yosida generation theorems.
* [Linares] F. Linares, "The Hille-Yosida Theorem", IMPA lecture notes (2021).
* [Baudoin] F. Baudoin, "Semigroups in Banach spaces", lecture notes (2019).
* Hille, "Functional Analysis and Semi-Groups" (1948).
* Yosida, "On the differentiability and the representation of one-parameter
  semi-group of linear operators" (1948).
* Reed-Simon, "Methods of Modern Mathematical Physics I", §VIII.
-/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

open scoped Topology NNReal

/-! ## Strongly Continuous Semigroups -/

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

-- Needed for `integral_smul` in the resolvent definition; not auto-synthesized
-- at `maxSynthPendingDepth = 3`.
instance : SMulCommClass ℝ ℝ X := smulCommClass_self ℝ X

/-- A strongly continuous one-parameter semigroup (C₀-semigroup) on a Banach space
([EN] Def. I.5.1, [Linares] Def. 1).

`S(t)` is a bounded linear operator for each `t ≥ 0`, satisfying:
1. `S(0) = Id`
2. `S(s + t) = S(s) ∘ S(t)` for all `s, t ≥ 0`
3. `t ↦ S(t) x` is continuous at `t = 0` for each `x : X`

By the semigroup property + continuity at 0, condition 3 is equivalent to
`t ↦ S(t) x` being continuous on all of `[0, ∞)`. -/
structure StronglyContinuousSemigroup where
  /-- The semigroup operator at time `t`. -/
  operator : ℝ → X →L[ℝ] X
  /-- `S(0) = Id` -/
  at_zero : operator 0 = ContinuousLinearMap.id ℝ X
  /-- `S(s + t) = S(s) ∘ S(t)` for `s, t ≥ 0` -/
  semigroup : ∀ (s t : ℝ), 0 ≤ s → 0 ≤ t →
    operator (s + t) = (operator s).comp (operator t)
  /-- Strong continuity: `t ↦ S(t) x` is continuous at 0 for each `x` -/
  strong_cont : ∀ (x : X), Filter.Tendsto
    (fun t => operator t x) (nhdsWithin 0 (Set.Ici 0)) (nhds x)

/-- A contraction semigroup: `‖S(t)‖ ≤ 1` for all `t ≥ 0`
([EN] Def. I.5.6, [Linares] Def. 3). Corresponds to growth bound `ω₀ = 0`. -/
structure ContractingSemigroup extends StronglyContinuousSemigroup X where
  /-- `‖S(t)‖ ≤ 1` for all `t ≥ 0`. -/
  contracting : ∀ (t : ℝ), 0 ≤ t → ‖operator t‖ ≤ 1

variable {X}

/-! ## Basic Properties -/

/-- `S(t) x` at `t = 0` equals `x`, pointwise version. -/
@[simp]
theorem StronglyContinuousSemigroup.operatorZeroApply
    (S : StronglyContinuousSemigroup X) (x : X) :
    S.operator 0 x = x := by
  rw [S.at_zero, ContinuousLinearMap.id_apply]

/-- The operator norm of a C₀-semigroup is bounded on `[0, 1]`.

This is one direction of [EN] Prop. I.5.3: strong continuity implies uniform
boundedness on compact intervals. The proof applies the Banach-Steinhaus
theorem (uniform boundedness principle) to the family `{S(t) : t ∈ [0,1]}`,
using strong continuity at 0 and the semigroup property to establish the
required pointwise bounds. -/
private theorem StronglyContinuousSemigroup.normBoundedOnUnitInterval
    (S : StronglyContinuousSemigroup X) :
    ∃ (M : ℝ), 1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ‖S.operator t‖ ≤ M := by
  -- Step 1: For each x, the orbit {S(t)x : t ∈ [0, 1]} is pointwise bounded.
  have h_ptwise : ∀ x : X, ∃ C, ∀ (i : Set.Icc (0 : ℝ) 1),
      ‖(fun j : Set.Icc (0 : ℝ) 1 => S.operator j.val) i x‖ ≤ C := by
    intro x
    -- By strong continuity at 0: S(t)x → x, so ‖S(t)x‖ bounded near 0
    have hsc := S.strong_cont x
    rw [Metric.tendsto_nhdsWithin_nhds] at hsc
    obtain ⟨δ, hδ_pos, hδ⟩ := hsc 1 one_pos
    -- ‖S(t)x‖ ≤ ‖x‖ + 1 for t ∈ [0, δ)
    have h_near : ∀ t : ℝ, 0 ≤ t → t < δ → ‖S.operator t x‖ ≤ ‖x‖ + 1 := by
      intro t ht0 htδ
      have h1 := hδ ht0 (by rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0])
      rw [dist_eq_norm] at h1
      linarith [norm_le_insert' (S.operator t x) x]
    -- Extend to [0, 1] using semigroup property and operator norm of S(δ)
    set L := max ‖S.operator δ‖ 1
    set B := ‖x‖ + 1
    set N := Nat.ceil (1 / δ)
    -- Claim: ∀ k, t ∈ [0, (k+1)δ) → ‖S(t)x‖ ≤ L^k * B
    have h_claim : ∀ (k : ℕ), ∀ t : ℝ, 0 ≤ t → t < (↑k + 1) * δ →
        ‖S.operator t x‖ ≤ L ^ k * B := by
      intro k; induction k with
      | zero =>
        intro t ht0 htδ
        simp only [Nat.cast_zero, zero_add, one_mul] at htδ
        simp only [pow_zero, one_mul]
        exact h_near t ht0 htδ
      | succ k ih =>
        intro t ht0 ht_ub
        by_cases hk : t < (↑k + 1) * δ
        · -- Earlier interval: use IH + L ≥ 1
          calc ‖S.operator t x‖ ≤ L ^ k * B := ih t ht0 hk
            _ ≤ L ^ (k + 1) * B := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact pow_le_pow_right₀ (le_max_right _ _) (Nat.le_succ k)
        · -- New interval: S(t)x = S(δ)(S(t-δ)x)
          push_neg at hk
          have htd_nn : 0 ≤ t - δ := by
            have : δ ≤ (↑k + 1) * δ :=
              le_mul_of_one_le_left (le_of_lt hδ_pos)
                (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ ↑k); linarith)
            linarith
          have htd_lt : t - δ < (↑k + 1) * δ := by
            push_cast [Nat.succ_eq_add_one] at ht_ub; linarith
          have h_sg := S.semigroup δ (t - δ) (le_of_lt hδ_pos) htd_nn
          rw [show δ + (t - δ) = t from by ring] at h_sg
          calc ‖S.operator t x‖
              = ‖S.operator δ (S.operator (t - δ) x)‖ := by
                simp only [h_sg, ContinuousLinearMap.comp_apply]
            _ ≤ ‖S.operator δ‖ * ‖S.operator (t - δ) x‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ L * (L ^ k * B) := by
                apply mul_le_mul (le_max_left _ _) (ih _ htd_nn htd_lt)
                  (by positivity) (by positivity)
            _ = L ^ (k + 1) * B := by ring
    -- For t ∈ [0, 1]: use claim with k = N, since 1 < (N+1)δ
    have hNδ : 1 < (↑N + 1) * δ := by
      have hN : (1 : ℝ) / δ ≤ ↑N := Nat.le_ceil _
      have : 1 ≤ ↑N * δ := by rwa [div_le_iff₀ hδ_pos] at hN
      linarith
    exact ⟨L ^ N * B, fun ⟨t, ht0, ht1⟩ => by
      simp only; exact h_claim N t ht0 (by linarith)⟩
  -- Step 2: Apply Banach-Steinhaus for uniform bound
  obtain ⟨C, hC⟩ := banach_steinhaus h_ptwise
  exact ⟨max C 1, le_max_right _ _, fun t ht0 ht1 =>
    (hC ⟨t, ht0, ht1⟩).trans (le_max_left _ _)⟩

/-- The operator norm of a C₀-semigroup is bounded on `[0, n]` for any `n : ℕ`.

Proof: by induction on `n`. For `t ∈ (k, k+1]`, write `t = (t-k) + k` where
`t - k ∈ [0, 1]`, so `S(t) = S(t-k) ∘ S(k)` and
`‖S(t)‖ ≤ ‖S(t-k)‖ · ‖S(k)‖ ≤ M · M^k = M^(k+1)`. -/
private theorem StronglyContinuousSemigroup.normBoundedOnInterval
    (S : StronglyContinuousSemigroup X) (n : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (t : ℝ), 0 ≤ t → t ≤ n → ‖S.operator t‖ ≤ C := by
  obtain ⟨M, hM1, hMbound⟩ := S.normBoundedOnUnitInterval
  have hM_pos : (0 : ℝ) < M := by linarith
  induction n with
  | zero =>
    refine ⟨1, one_pos, fun t ht htn => ?_⟩
    simp only [Nat.cast_zero] at htn
    have : t = 0 := le_antisymm htn ht
    rw [this, S.at_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    obtain ⟨C_k, hC_k_pos, hC_k_bound⟩ := ih
    refine ⟨M * C_k, mul_pos hM_pos hC_k_pos, fun t ht htn => ?_⟩
    by_cases hk : t ≤ ↑k
    · calc ‖S.operator t‖ ≤ C_k := hC_k_bound t ht hk
        _ ≤ M * C_k := le_mul_of_one_le_left (le_of_lt hC_k_pos) hM1
    · -- t ∈ (k, k+1], decompose: t = (t - k) + k
      push_neg at hk
      have htk_nn : 0 ≤ t - ↑k := by linarith
      have htk_le : t - ↑k ≤ 1 := by
        push_cast [Nat.succ_eq_add_one] at htn; linarith
      have hk_nn : (0 : ℝ) ≤ ↑k := Nat.cast_nonneg k
      have h_eq : t = (t - ↑k) + ↑k := by ring
      have h_sg := S.semigroup (t - ↑k) ↑k htk_nn hk_nn
      rw [← h_eq] at h_sg
      rw [h_sg]
      calc ‖(S.operator (t - ↑k)).comp (S.operator ↑k)‖
          ≤ ‖S.operator (t - ↑k)‖ * ‖S.operator ↑k‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * C_k :=
            mul_le_mul (hMbound _ htk_nn htk_le) (hC_k_bound ↑k hk_nn le_rfl)
              (norm_nonneg _) (le_of_lt hM_pos)

/-- Strong continuity at every `t₀ ≥ 0`, not just at 0
([EN] Prop. I.5.3, [Linares] Cor. 1).

From continuity at 0: `S(t)x → x` as `t → 0⁺`. Then at `t₀`:
`S(t₀ + h)x = S(t₀)(S(h)x) → S(t₀)x` as `h → 0⁺` by continuity of `S(t₀)`.
Left continuity uses the operator norm bound from `normBoundedOnInterval`. -/
theorem StronglyContinuousSemigroup.strongContAt
    (S : StronglyContinuousSemigroup X) (x : X) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    Filter.Tendsto (fun t => S.operator t x)
      (nhdsWithin t₀ (Set.Ici 0)) (nhds (S.operator t₀ x)) := by
  -- Decompose nhdsWithin t₀ (Ici 0) using Iic/Ici splitting at t₀.
  -- nhdsWithin t₀ (Ici 0) = nhdsWithin t₀ (Ici 0 ∩ Iic t₀) ⊔ nhdsWithin t₀ (Ici 0 ∩ Ici t₀)
  rw [show Set.Ici (0 : ℝ) = (Set.Ici 0 ∩ Set.Iic t₀) ∪ (Set.Ici 0 ∩ Set.Ici t₀) from by
    rw [← Set.inter_union_distrib_left, Set.Iic_union_Ici, Set.inter_univ]]
  rw [nhdsWithin_union, Filter.tendsto_sup]
  -- Simplify the intersection sets
  have h_right_set : Set.Ici (0 : ℝ) ∩ Set.Ici t₀ = Set.Ici t₀ := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Ici]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨le_trans ht₀ h, h⟩⟩
  have h_left_set : Set.Ici (0 : ℝ) ∩ Set.Iic t₀ = Set.Icc 0 t₀ :=
    Set.Ici_inter_Iic
  rw [h_left_set, h_right_set]
  constructor
  · -- Left continuity: nhdsWithin t₀ (Icc 0 t₀)
    -- For 0 ≤ t ≤ t₀: S(t₀)x = S(t)(S(t₀-t)x), so
    -- S(t)x - S(t₀)x = S(t)(x - S(t₀-t)x).
    -- ‖S(t)(x - S(t₀-t)x)‖ ≤ ‖S(t)‖·‖x - S(t₀-t)x‖ → 0
    -- since ‖S(t)‖ is bounded on [0, t₀] and ‖S(t₀-t)x - x‖ → 0.
    -- The operator norm bound on [0, t₀] follows from normBoundedOnUnitInterval
    -- (itself proved via the uniform boundedness principle) + the semigroup property.
    -- We state this bound as a local fact.
    have h_norm_bound : ∃ C > 0, ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ‖S.operator t‖ ≤ C := by
      obtain ⟨C, hC, hCb⟩ := S.normBoundedOnInterval (Nat.ceil t₀)
      exact ⟨C, hC, fun t ht ht' => hCb t ht (ht'.trans (Nat.le_ceil t₀))⟩
    obtain ⟨C, hC_pos, hC_bound⟩ := h_norm_bound
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    -- Extract δ from strong_cont: for h ∈ [0, δ), ‖S(h)x - x‖ < ε/C
    have h_sc := S.strong_cont x
    rw [Metric.tendsto_nhdsWithin_nhds] at h_sc
    obtain ⟨δ, hδ_pos, hδ_spec⟩ := h_sc (ε / C) (div_pos hε hC_pos)
    refine ⟨δ, hδ_pos, fun t ht_mem ht_dist => ?_⟩
    simp only [Set.mem_Icc] at ht_mem
    -- Key: S(t₀)x = S(t)(S(t₀ - t)x) by semigroup
    have ht₀t_nn : 0 ≤ t₀ - t := by linarith [ht_mem.2]
    have h_sg_eq : S.operator t₀ = (S.operator t).comp (S.operator (t₀ - t)) := by
      have := S.semigroup t (t₀ - t) ht_mem.1 ht₀t_nn
      rwa [add_sub_cancel] at this
    -- S(t)x - S(t₀)x = S(t)(x - S(t₀-t)x)
    have h_diff : S.operator t x - S.operator t₀ x =
        S.operator t (x - S.operator (t₀ - t) x) := by
      conv_rhs => rw [map_sub]
      congr 1
      rw [h_sg_eq, ContinuousLinearMap.comp_apply]
    rw [dist_eq_norm, h_diff]
    calc ‖S.operator t (x - S.operator (t₀ - t) x)‖
        ≤ ‖S.operator t‖ * ‖x - S.operator (t₀ - t) x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖x - S.operator (t₀ - t) x‖ :=
          mul_le_mul_of_nonneg_right (hC_bound t ht_mem.1 ht_mem.2) (norm_nonneg _)
      _ = C * dist (S.operator (t₀ - t) x) x := by
          rw [dist_eq_norm, ← norm_neg, neg_sub]
      _ < C * (ε / C) := by
          apply mul_lt_mul_of_pos_left _ hC_pos
          apply hδ_spec ht₀t_nn
          simp only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht₀t_nn]
          rw [Real.dist_eq, abs_sub_comm] at ht_dist
          rwa [abs_of_nonneg ht₀t_nn] at ht_dist
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hC_pos)
  · -- Right continuity: nhdsWithin t₀ (Ici t₀)
    -- For t ≥ t₀: S(t)x = S(t₀)(S(t - t₀)x) and S(t-t₀)x → x by strong_cont.
    -- S(t₀) is a CLM, hence continuous, so S(t₀)(S(t-t₀)x) → S(t₀)x.
    -- The map t ↦ t - t₀ sends nhdsWithin t₀ (Ici t₀) to nhdsWithin 0 (Ici 0)
    have h_sub_tendsto : Filter.Tendsto (fun t => t - t₀)
        (nhdsWithin t₀ (Set.Ici t₀)) (nhdsWithin 0 (Set.Ici 0)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Filter.Tendsto (fun t => t - t₀) (nhds t₀) (nhds 0) := by
          have h := Filter.Tendsto.sub_const (Filter.tendsto_id (α := ℝ).mono_left
            (le_refl (nhds t₀))) t₀
          simp only [id, sub_self] at h; exact h
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_Ici] at ht ⊢; linarith
    -- So S(t - t₀)x → x
    have h_inner : Filter.Tendsto (fun t => S.operator (t - t₀) x)
        (nhdsWithin t₀ (Set.Ici t₀)) (nhds x) := (S.strong_cont x).comp h_sub_tendsto
    -- And S(t₀)(S(t - t₀)x) → S(t₀)x by continuity of the CLM S(t₀)
    have h_outer : Filter.Tendsto (fun t => S.operator t₀ (S.operator (t - t₀) x))
        (nhdsWithin t₀ (Set.Ici t₀)) (nhds (S.operator t₀ x)) :=
      ((S.operator t₀).cont.tendsto x).comp h_inner
    -- It suffices to show S(t)x = S(t₀)(S(t - t₀)x) for t ≥ t₀
    apply h_outer.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Ici] at ht
    have ht_nn : 0 ≤ t - t₀ := by linarith
    -- S(t₀ + (t - t₀)) = S(t₀) ∘ S(t - t₀) by semigroup, and t₀ + (t - t₀) = t
    have h_sg := S.semigroup t₀ (t - t₀) ht₀ ht_nn
    rw [show t₀ + (t - t₀) = t from by ring] at h_sg
    change (S.operator t₀) ((S.operator (t - t₀)) x) = (S.operator t) x
    rw [h_sg, ContinuousLinearMap.comp_apply]

/-! ## The Infinitesimal Generator -/

/-- The infinitesimal generator of a C₀-semigroup ([EN] Def. II.1.2,
[Linares] Def. 2). The domain consists of elements `x` for which the
limit `lim_{t→0⁺} (S(t)x - x)/t` exists. The generator `A` is the
value of this limit. By [EN] Thm. II.1.4, `A` is closed, densely defined,
and determines the semigroup uniquely. -/
def StronglyContinuousSemigroup.generator (S : StronglyContinuousSemigroup X)
    (x : X) : Prop :=
  ∃ (Ax : X), Filter.Tendsto
    (fun t => (1/t) • (S.operator t x - x))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds Ax)

/-- The domain of the generator as a ℝ-submodule of X.

This is algebraically closed under addition and scalar multiplication because
limits of sums/scalar-multiples are sums/scalar-multiples of limits
(in the Hausdorff topology of a Banach space). -/
def StronglyContinuousSemigroup.domain (S : StronglyContinuousSemigroup X) :
    Submodule ℝ X where
  carrier := { x | S.generator x }
  add_mem' := by
    intro x y hx hy
    obtain ⟨Ax, hAx⟩ := hx
    obtain ⟨Ay, hAy⟩ := hy
    refine ⟨Ax + Ay, ?_⟩
    have : Filter.Tendsto
        (fun t => (1/t) • (S.operator t (x + y) - (x + y)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Ax + Ay)) := by
      have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          (1/t) • (S.operator t (x + y) - (x + y)) =
            (1/t) • (S.operator t x - x) + (1/t) • (S.operator t y - y) := by
        filter_upwards with t
        rw [map_add, add_sub_add_comm, smul_add]
      exact (hAx.add hAy).congr' (heq.mono (fun _ h => h.symm))
    exact this
  zero_mem' := by
    refine ⟨0, ?_⟩
    have : (fun t => (1/t) • (S.operator t (0 : X) - 0)) = fun _ => 0 := by
      ext t; simp [map_zero]
    rw [this]; exact tendsto_const_nhds
  smul_mem' := by
    intro c x hx
    obtain ⟨Ax, hAx⟩ := hx
    refine ⟨c • Ax, ?_⟩
    have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        (1/t) • (S.operator t (c • x) - c • x) =
          c • ((1/t) • (S.operator t x - x)) := by
      filter_upwards with t
      simp only [map_smul, smul_sub, smul_comm c (1/t)]
    exact (hAx.const_smul c).congr' (heq.mono (fun _ h => h.symm))

/-- The infinitesimal generator `A`, as a linear map from its domain submodule to `X`.

Uses `Classical.choose` to extract the limit value. Linearity follows from
uniqueness of limits in a Hausdorff space (`tendsto_nhds_unique`). -/
noncomputable def StronglyContinuousSemigroup.generatorMap
    (S : StronglyContinuousSemigroup X) : S.domain →ₗ[ℝ] X where
  toFun := fun x => Classical.choose x.property
  map_add' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    have hAx := Classical.choose_spec hx
    have hAy := Classical.choose_spec hy
    have hxy := Classical.choose_spec (S.domain.add_mem hx hy)
    have hsum : Filter.Tendsto
        (fun t => (1/t) • (S.operator t (x + y) - (x + y)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Classical.choose hx + Classical.choose hy)) := by
      have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          (1/t) • (S.operator t (x + y) - (x + y)) =
            (1/t) • (S.operator t x - x) + (1/t) • (S.operator t y - y) := by
        filter_upwards with t; rw [map_add, add_sub_add_comm, smul_add]
      exact (hAx.add hAy).congr' (heq.mono (fun _ h => h.symm))
    exact tendsto_nhds_unique hxy hsum
  map_smul' := by
    intro c ⟨x, hx⟩
    have hAx := Classical.choose_spec hx
    have hcx := Classical.choose_spec (S.domain.smul_mem c hx)
    have hscaled : Filter.Tendsto
        (fun t => (1/t) • (S.operator t (c • x) - c • x))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (c • Classical.choose hx)) := by
      have heq : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
          (1/t) • (S.operator t (c • x) - c • x) =
            c • ((1/t) • (S.operator t x - x)) := by
        filter_upwards with t
        simp only [map_smul, smul_sub, smul_comm c (1/t)]
      exact (hAx.const_smul c).congr' (heq.mono (fun _ h => h.symm))
    exact tendsto_nhds_unique hcx hscaled

/-! ## The Resolvent (for Contraction Semigroups) -/

open MeasureTheory

/-- The pointwise integrand of the Laplace transform is integrable on `(0, ∞)`.

For a **contraction** semigroup (`‖S(t)‖ ≤ 1`), the integrand satisfies
`‖e^{-λt} S(t) x‖ ≤ e^{-λt} ‖x‖`, which is integrable for `λ > 0`.

**Why contraction?** A general C₀-semigroup can have exponential growth
`‖S(t)‖ ≤ M e^{ωt}`. If `λ ≤ ω`, the integrand diverges and the Bochner
integral returns junk (zero). This breaks `integral_add` (which requires
both summands to be `Integrable`), making it impossible to prove linearity
of the resolvent. Restricting to contractions (`ω = 0`) ensures `λ > 0`
suffices for convergence. -/
lemma ContractingSemigroup.integrable_resolvent_integrand
    (S : ContractingSemigroup X) (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    IntegrableOn (fun t => Real.exp (-(lambda * t)) • S.operator t x)
      (Set.Ioi 0) := by
  unfold MeasureTheory.IntegrableOn
  -- Bound by ‖x‖ * exp(-λt), which is integrable for λ > 0
  apply MeasureTheory.Integrable.mono'
    ((exp_neg_integrableOn_Ioi 0 hlam).smul (‖x‖))
  · -- AEStronglyMeasurable: follows from ContinuousOn → measurable
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul
    · -- exp(-λt) is continuous everywhere, hence on Ioi 0
      exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).continuousOn
    · -- S(t)x is continuous on [0, ∞) by strongContAt, hence on (0, ∞)
      have h_cont : ContinuousOn (fun t => S.operator t x) (Set.Ici 0) :=
        fun t₀ ht₀ => S.toStronglyContinuousSemigroup.strongContAt x t₀ ht₀
      exact h_cont.mono Set.Ioi_subset_Ici_self
  · -- Norm bound: ‖exp(-λt) • S(t)x‖ ≤ ‖x‖ * exp(-λt) a.e. on Ioi 0
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t (ht : 0 < t)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Pi.smul_apply, smul_eq_mul]
    calc Real.exp (-(lambda * t)) * ‖(S.operator t) x‖
        ≤ Real.exp (-(lambda * t)) * (‖S.operator t‖ * ‖x‖) := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.exp (-(lambda * t)) * (1 * ‖x‖) := by
          gcongr; exact S.contracting t (le_of_lt ht)
      _ = ‖x‖ * Real.exp (-(lambda * t)) := by ring
      _ = ‖x‖ * Real.exp (-lambda * t) := by rw [neg_mul]

/-- The resolvent operator `R(λ) x = ∫₀^∞ e^{-λt} S(t)x dt` for `λ > 0`.

Defined on **contraction semigroups** to guarantee integrability (see
`integrable_resolvent_integrand`). Constructed via `LinearMap.mkContinuous`
which simultaneously provides the linear map and the operator norm bound
`‖R(λ)‖ ≤ 1/λ`.

**Implementation note**: The integral is defined pointwise for each `x ∈ X`,
not as an operator-valued integral. This is necessary because `t ↦ S(t)` is
only strongly continuous, so `t ↦ S(t)` is not strongly measurable as a
function into `X →L[ℝ] X`. The pointwise integral `x ↦ ∫ e^{-λt} S(t)x dt`
is well-defined because `t ↦ S(t)x` IS strongly measurable for each `x`. -/
noncomputable def ContractingSemigroup.resolvent
    (S : ContractingSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) : X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun x =>
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lambda * t)) • S.operator t x
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact integral_add
          (S.integrable_resolvent_integrand lambda hlam x)
          (S.integrable_resolvent_integrand lambda hlam y)
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, map_smul]
        have h : ∀ t : ℝ, Real.exp (-(lambda * t)) • c • (S.operator t) x =
            c • (Real.exp (-(lambda * t)) • (S.operator t) x) :=
          fun t => smul_comm _ c _
        simp_rw [h]
        exact integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ))) c
          (fun t => Real.exp (-(lambda * t)) • (S.operator t) x) }
    (1 / lambda)
    (by
      intro x; simp only [LinearMap.coe_mk, AddHom.coe_mk]
      -- ‖∫ exp(-λt) • S(t)x‖ ≤ (1/λ) * ‖x‖
      -- Step 1: bound the norm of the integral
      calc ‖∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) • (S.operator t) x‖
          ≤ ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) * ‖x‖ := by
            apply MeasureTheory.norm_integral_le_of_norm_le
            · -- Integrability of exp(-λt) * ‖x‖ on Ioi 0
              have h := (exp_neg_integrableOn_Ioi 0 hlam).integrable.mul_const ‖x‖
              simp only [neg_mul] at h; exact h
            · apply (ae_restrict_mem measurableSet_Ioi).mono
              intro t (ht : 0 < t)
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              gcongr
              calc ‖(S.operator t) x‖
                  ≤ ‖S.operator t‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ 1 * ‖x‖ := by gcongr; exact S.contracting t (le_of_lt ht)
                _ = ‖x‖ := one_mul _
        -- Step 2: evaluate ∫ exp(-λt) * ‖x‖ = (1/λ) * ‖x‖
        _ = 1 / lambda * ‖x‖ := by
            -- Pull out constant ‖x‖
            -- Evaluate ∫ exp(-λt) = 1/λ via substitution
            have h_eval : ∫ t in Set.Ioi 0, Real.exp (-(lambda * t)) = lambda⁻¹ := by
              have h := integral_comp_mul_left_Ioi (fun t => Real.exp (-t)) 0 hlam
              simp only [mul_zero] at h
              rw [h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]
            -- Pull constant ‖x‖ out and apply evaluation
            rw [show (fun t => Real.exp (-(lambda * t)) * ‖x‖) =
                (fun t => ‖x‖ • Real.exp (-(lambda * t))) from by ext; simp [mul_comm]]
            rw [integral_smul (μ := volume.restrict (Set.Ioi (0 : ℝ)))]
            simp only [smul_eq_mul, h_eval, one_div]
            ring
            )

/-! ## Resolvent-Generator Interface

The proofs of `resolventMapsToDomain` and `resolventRightInv` use the integral
shift trick from [EN] Thm. II.1.10(i) / [Linares] eq. 0.15. We first establish
helper lemmas for the key computation. -/

/-- Translation of set integral: `∫_{Ioi 0} f(t + h) = ∫_{Ioi h} f(u)`.
Follows from translation invariance of Lebesgue measure. -/
private lemma integral_comp_add_right_Ioi (f : ℝ → X) (h : ℝ) :
    ∫ t in Set.Ioi 0, f (t + h) = ∫ u in Set.Ioi h, f u := by
  -- Uses: MeasurableEmbedding of (· + h), Measure.map_add_right_eq_self,
  -- and (· + h) '' Ioi 0 = Ioi h.
  sorry

/-- Splitting `∫_{Ioi 0} = ∫_{Ioc 0 h} + ∫_{Ioi h}` for `h > 0`. -/
private lemma integral_Ioi_eq_Ioc_add_Ioi (f : ℝ → X) {h : ℝ} (hh : 0 < h)
    (hf : IntegrableOn f (Set.Ioi 0) volume) :
    ∫ t in Set.Ioi 0, f t = (∫ t in Set.Ioc 0 h, f t) + ∫ t in Set.Ioi h, f t := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hh)]
  have hd : Disjoint (Set.Ioc 0 h) (Set.Ioi h) :=
    Set.disjoint_left.mpr (fun _ ht1 ht2 => not_le.mpr ht2 ht1.2)
  exact MeasureTheory.setIntegral_union hd measurableSet_Ioi
    (hf.mono_set Set.Ioc_subset_Ioi_self)
    (hf.mono_set (Set.Ioi_subset_Ioi (le_of_lt hh)))

/-- The resolvent maps all of `X` into the domain of the generator.

This is part of the proof that `R(λ)` is the two-sided inverse of `λI - A`
(eq. 0.15–0.16 in [Linares]). The key computation shows the generator
difference quotient `(S(h) - I)/h · R(λ)x` converges as `h → 0⁺` to
`λ R(λ)x - x`, simultaneously proving domain membership and the value
of `A R(λ)x`.

Proof outline (eq. 0.15 in [Linares]):
  `(T(h) - I)/h · R_λ x = (e^{λh} - 1)/h · ∫₀^∞ e^{-λt} T(t)x dt
                          - e^{λh}/h · ∫₀ʰ e^{-λt} T(t)x dt`
  As `h → 0⁺`: first term → `λ R_λ x`, second term → `x`. -/
theorem ContractingSemigroup.resolventMapsToDomain
    (S : ContractingSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    (S.resolvent lambda hlam x) ∈
      S.toStronglyContinuousSemigroup.domain := by
  -- Provide the limit value: A(R_λ x) = λ R_λ x - x
  set Rlx := S.resolvent lambda hlam x
  refine ⟨lambda • Rlx - x, ?_⟩
  -- Need: (1/h) • (S(h)(Rlx) - Rlx) → λ Rlx - x as h → 0⁺
  -- Key identity for h > 0 ([EN] Thm. II.1.10(i), [Linares] eq. 0.15):
  --   S(h)(Rlx) - Rlx = (e^{λh} - 1) • Rlx - e^{λh} • ∫₀ʰ e^{-λt} S(t)x dt
  -- Dividing by h and taking h → 0⁺:
  --   (e^{λh}-1)/h → λ and (1/h)∫₀ʰ e^{-λt} S(t)x dt → x
  sorry

/-- The fundamental resolvent identity: `(λI - A) R(λ) x = x`.

This is eq. 0.16 in [Linares]: the resolvent `R_λ = (λI - A)⁻¹` is the
right inverse of `λI - A`. Combined with `resolventMapsToDomain`, this
shows `R_λ` is the bounded inverse of `λI - A` on all of `X`, establishing
that `(0, ∞) ⊂ ρ(A)` (the resolvent set).

The proof follows from the same integral shift computation as
`resolventMapsToDomain` (eq. 0.15 in [Linares]): the limit
`lim_{h→0⁺} (S(h) - I)/h · R(λ)x = λ R(λ)x - x` gives both the domain
membership and the identity `A R(λ)x = λ R(λ)x - x`, which rearranges to
`(λI - A) R(λ) x = x`. -/
theorem ContractingSemigroup.resolventRightInv
    (S : ContractingSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    let Rlx := S.resolvent lambda hlam x
    let Rlx_dom : S.toStronglyContinuousSemigroup.domain :=
      ⟨Rlx, S.resolventMapsToDomain lambda hlam x⟩
    lambda • Rlx - S.toStronglyContinuousSemigroup.generatorMap Rlx_dom = x := by
  -- Follows from the same computation as resolventMapsToDomain:
  -- The limit (1/h)(S(h)(R_λ x) - R_λ x) → λ R_λ x - x shows that
  -- A(R_λ x) = λ R_λ x - x (by tendsto_nhds_unique), hence
  -- λ R_λ x - A(R_λ x) = x.
  sorry

/-! ## Hille-Yosida Theorem -/

/-- **Hille-Yosida resolvent bound** (forward direction).

For a contraction semigroup, the resolvent `R(λ) = ∫₀^∞ e^{-λt} S(t) dt`
satisfies `‖R(λ)‖ ≤ 1/λ` for all `λ > 0`.

This is essentially free from the construction: `resolvent` was built via
`LinearMap.mkContinuous` with bound `1/λ`, so the norm bound follows from
`LinearMap.mkContinuous_norm_le`.

This is the forward direction of the Hille-Yosida theorem. The full theorem
(an operator A generates a contraction semigroup iff it is closed, densely
defined, with `‖(λI - A)⁻¹‖ ≤ 1/λ`) requires the converse: constructing
the semigroup from the operator, which needs the Yosida approximation.

Ref: Hille (1948), Yosida (1948); Reed-Simon I §VIII.3; Engel-Nagel Ch. II -/
theorem hilleYosidaResolventBound
    (S : ContractingSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) :
    ‖S.resolvent lambda hlam‖ ≤ 1 / lambda :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-! ## Growth Bounds and Exponential Type -/

/-- A C₀-semigroup has exponential growth bound `ω` if `‖S(t)‖ ≤ M e^{ωt}`
for some constant `M ≥ 1` ([EN] eq. I.(5.1)). Contraction semigroups have
`M = 1, ω = 0`. The infimum of all such `ω` is the growth bound `ω₀`
([EN] Def. I.5.6). -/
def StronglyContinuousSemigroup.HasGrowthBound
    (S : StronglyContinuousSemigroup X) (ω : ℝ) (M : ℝ) : Prop :=
  1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → ‖S.operator t‖ ≤ M * Real.exp (ω * t)

/-- Every C₀-semigroup has a finite exponential growth bound
([EN] Prop. I.5.5, [Linares] Thm. 1). The proof uses the uniform
bound `M` on `[0, 1]` and sets `ω = log M`, then decomposes
`t = ⌊t⌋ + frac(t)` to get `‖S(t)‖ ≤ M^{⌊t⌋+1} ≤ M · e^{ωt}`. -/
theorem StronglyContinuousSemigroup.existsGrowthBound
    (S : StronglyContinuousSemigroup X) :
    ∃ (ω : ℝ) (M : ℝ), S.HasGrowthBound ω M := by
  obtain ⟨M, hM1, hMbound⟩ := S.normBoundedOnUnitInterval
  have hM_pos : 0 < M := by linarith
  refine ⟨Real.log M, M, hM1, fun t ht => ?_⟩
  -- Integer-time operator norm bound by induction: ‖S(k)‖ ≤ M^k
  have h_int_bound : ∀ (k : ℕ), ‖S.operator (↑k : ℝ)‖ ≤ M ^ k := by
    intro k; induction k with
    | zero =>
      simp only [Nat.cast_zero, S.at_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      have : (↑(k + 1) : ℝ) = 1 + ↑k := by push_cast; ring
      rw [this, S.semigroup 1 ↑k (by linarith) (Nat.cast_nonneg k)]
      calc ‖(S.operator 1).comp (S.operator ↑k)‖
          ≤ ‖S.operator 1‖ * ‖S.operator ↑k‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * M ^ k :=
            mul_le_mul (hMbound 1 (by linarith) le_rfl) ih (norm_nonneg _) (by linarith)
        _ = M ^ (k + 1) := by ring
  -- Decompose t = (t - ⌊t⌋₊) + ⌊t⌋₊ where 0 ≤ t - ⌊t⌋₊ ≤ 1
  set n := ⌊t⌋₊ with hn_def
  have hn_le : (↑n : ℝ) ≤ t := Nat.floor_le ht
  have hfrac_nn : 0 ≤ t - ↑n := sub_nonneg.mpr hn_le
  have hfrac_le1 : t - ↑n ≤ 1 := by
    have := Nat.lt_floor_add_one t; push_cast at this ⊢; linarith
  -- Use semigroup property: S(t) = S(t - n) ∘ S(n)
  have h_eq : (t - ↑n) + ↑n = t := by ring
  have h_sg := S.semigroup (t - ↑n) ↑n hfrac_nn (Nat.cast_nonneg n)
  rw [h_eq] at h_sg
  rw [h_sg]
  -- ‖S(t-n) ∘ S(n)‖ ≤ ‖S(t-n)‖ · ‖S(n)‖ ≤ M · M^n ≤ M · exp(log M · t)
  calc ‖(S.operator (t - ↑n)).comp (S.operator ↑n)‖
      ≤ ‖S.operator (t - ↑n)‖ * ‖S.operator ↑n‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * M ^ n :=
        mul_le_mul (hMbound _ hfrac_nn hfrac_le1) (h_int_bound n) (norm_nonneg _) (by linarith)
    _ ≤ M * Real.exp (Real.log M * t) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc (M : ℝ) ^ n
            = Real.exp (↑n * Real.log M) := by
              rw [Real.exp_nat_mul, Real.exp_log hM_pos]
          _ ≤ Real.exp (Real.log M * t) := by
              apply Real.exp_le_exp.mpr
              calc ↑n * Real.log M ≤ t * Real.log M :=
                    mul_le_mul_of_nonneg_right hn_le (Real.log_nonneg hM1)
                _ = Real.log M * t := by ring

end
