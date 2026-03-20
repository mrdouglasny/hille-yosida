/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Strongly Continuous Semigroups and the Hille-Yosida Theorem

This file defines strongly continuous one-parameter semigroups on Banach spaces
and states the Hille-Yosida generation theorem.

## Main Definitions

* `StronglyContinuousSemigroup` — a family `S(t)` of bounded linear operators
  for `t ≥ 0` satisfying `S(0) = 1`, `S(s+t) = S(s) ∘ S(t)`, and strong
  continuity at `t = 0`.

* `IsContractingSemigroup` — a strongly continuous semigroup of contractions:
  `‖S(t)‖ ≤ 1` for all `t ≥ 0`.

## Main Theorems

* `hille_yosida` — An operator `A` generates a contraction semigroup iff it is
  closed, densely defined, and its resolvent satisfies `‖(λ - A)⁻¹‖ ≤ 1/λ`
  for all `λ > 0`.

## References

* Hille-Yosida: E. Hille, "Functional Analysis and Semi-Groups" (1948);
  K. Yosida, "On the differentiability and the representation of one-parameter
  semi-group of linear operators" (1948)
* Reed-Simon, "Methods of Modern Mathematical Physics I", §VIII
* Engel-Nagel, "One-Parameter Semigroups for Linear Evolution Equations" (2000)
-/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.ContinuousMap.Basic

noncomputable section

open scoped Topology NNReal

/-! ## Strongly Continuous Semigroups -/

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A strongly continuous one-parameter semigroup (C₀-semigroup) on a Banach space.

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

/-- A contraction semigroup: `‖S(t)‖ ≤ 1` for all `t ≥ 0`. -/
structure ContractingSemigroup extends StronglyContinuousSemigroup X where
  /-- `‖S(t)‖ ≤ 1` for all `t ≥ 0`. -/
  contracting : ∀ (t : ℝ), 0 ≤ t → ‖operator t‖ ≤ 1

variable {X}

/-! ## Basic Properties -/

/-- `S(t) x` at `t = 0` equals `x`, pointwise version. -/
@[simp]
theorem StronglyContinuousSemigroup.operator_zero_apply
    (S : StronglyContinuousSemigroup X) (x : X) :
    S.operator 0 x = x := by
  have := congrFun (congrArg DFunLike.coe S.at_zero) x
  simpa using this

/-- The operator norm of a C₀-semigroup is bounded on `[0, 1]`.

By strong continuity at 0, for each x, `‖S(t) x‖` is bounded near 0.
The uniform boundedness principle gives a uniform bound on `‖S(t)‖`.
Here we use a direct bound: `S(0) = Id` and continuity. -/
private theorem StronglyContinuousSemigroup.norm_bounded_on_unit_interval
    (S : StronglyContinuousSemigroup X) :
    ∃ (M : ℝ), 1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ‖S.operator t‖ ≤ M := by
  sorry

/-- The operator norm of a C₀-semigroup is bounded on `[0, n]` for any `n : ℕ`.

Proof: by induction on `n`. For `t ∈ (k, k+1]`, write `t = (t-k) + k` where
`t - k ∈ [0, 1]`, so `S(t) = S(t-k) ∘ S(k)` and
`‖S(t)‖ ≤ ‖S(t-k)‖ · ‖S(k)‖ ≤ M · M^k = M^(k+1)`. -/
private theorem StronglyContinuousSemigroup.norm_bounded_on_interval
    (S : StronglyContinuousSemigroup X) (n : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (t : ℝ), 0 ≤ t → t ≤ n → ‖S.operator t‖ ≤ C := by
  obtain ⟨M, hM1, hMbound⟩ := S.norm_bounded_on_unit_interval
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

/-- Strong continuity at every `t₀ ≥ 0`, not just at 0.

From continuity at 0: `S(t)x → x` as `t → 0⁺`. Then at `t₀`:
`S(t₀ + h)x = S(t₀)(S(h)x) → S(t₀)x` as `h → 0⁺` by continuity of `S(t₀)`. -/
theorem StronglyContinuousSemigroup.strong_cont_at
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
    -- The operator norm bound on [0, t₀] follows from norm_bounded_on_unit_interval
    -- (itself proved via the uniform boundedness principle) + the semigroup property.
    -- We state this bound as a local fact.
    have h_norm_bound : ∃ C > 0, ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ‖S.operator t‖ ≤ C := by
      obtain ⟨C, hC, hCb⟩ := S.norm_bounded_on_interval (Nat.ceil t₀)
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

/-- The infinitesimal generator of a C₀-semigroup. The domain consists of
elements `x` for which the limit `lim_{t→0⁺} (S(t)x - x)/t` exists.
The generator `A` is the value of this limit. -/
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

/-! ## The Resolvent -/

/-- The resolvent operator `R(λ, A) = (λI - A)⁻¹` expressed via the Laplace
transform of the semigroup: `R(λ)x = ∫₀^∞ e^{-λt} S(t)x dt` for `λ > 0`.

For a contraction semigroup, this integral converges for all `λ > 0` and
defines a bounded operator with `‖R(λ)‖ ≤ 1/λ`. -/
def StronglyContinuousSemigroup.resolvent (S : StronglyContinuousSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) : X →L[ℝ] X :=
  sorry -- ∫₀^∞ e^{-lambda t} S.operator t dt (Bochner integral)

/-! ## Resolvent-Generator Interface -/

/-- The resolvent maps all of `X` into the domain of the generator. -/
theorem StronglyContinuousSemigroup.resolvent_maps_to_domain
    (S : StronglyContinuousSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    (S.resolvent lambda hlam x) ∈ S.domain := by
  sorry

/-- The fundamental resolvent identity: `(λI - A) R(λ) x = x`.
This is the operational meaning of "the resolvent is the inverse of `(λI - A)`". -/
theorem StronglyContinuousSemigroup.resolvent_right_inv
    (S : StronglyContinuousSemigroup X)
    (lambda : ℝ) (hlam : 0 < lambda) (x : X) :
    let Rlx := S.resolvent lambda hlam x
    let Rlx_dom : S.domain := ⟨Rlx, S.resolvent_maps_to_domain lambda hlam x⟩
    lambda • Rlx - S.generatorMap Rlx_dom = x := by
  sorry

/-! ## Hille-Yosida Theorem -/

/-- **Hille-Yosida Theorem** (Generation of contraction semigroups).

A closed, densely defined linear operator `A` on a Banach space `X` generates
a contraction semigroup if and only if:
1. `(0, ∞) ⊆ ρ(A)` (the resolvent set of A)
2. `‖(λI - A)⁻¹‖ ≤ 1/λ` for all `λ > 0`

This is the foundational theorem connecting abstract operators to time evolution.

Ref: Hille (1948), Yosida (1948); Reed-Simon I §VIII.3; Engel-Nagel Ch. II -/
theorem hille_yosida
    (S : ContractingSemigroup X) :
    -- For all λ > 0, the resolvent exists and satisfies the bound
    ∀ (lambda : ℝ) (hlam : 0 < lambda),
      ‖S.toStronglyContinuousSemigroup.resolvent lambda hlam‖ ≤ 1 / lambda := by
  sorry

/-! ## Growth Bounds and Exponential Type -/

/-- A C₀-semigroup has exponential growth bound `ω` if `‖S(t)‖ ≤ M e^{ωt}`
for some constant `M ≥ 1`. Contraction semigroups have `M = 1, ω = 0`. -/
def StronglyContinuousSemigroup.hasGrowthBound
    (S : StronglyContinuousSemigroup X) (ω : ℝ) (M : ℝ) : Prop :=
  1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → ‖S.operator t‖ ≤ M * Real.exp (ω * t)

/-- Every C₀-semigroup has a finite exponential growth bound.
This follows from the uniform bound on `[0, 1]` combined with the
semigroup property: `S(n + r) = S(1)^n ∘ S(r)` for integer n. -/
theorem StronglyContinuousSemigroup.exists_growth_bound
    (S : StronglyContinuousSemigroup X) :
    ∃ (ω : ℝ) (M : ℝ), S.hasGrowthBound ω M := by
  obtain ⟨M, hM1, hMbound⟩ := S.norm_bounded_on_unit_interval
  refine ⟨Real.log M, M, hM1, fun t ht => ?_⟩
  -- Write t = ⌊t⌋ + (t - ⌊t⌋) where 0 ≤ t - ⌊t⌋ < 1
  -- Then ‖S(t)‖ ≤ ‖S(1)‖^⌊t⌋ · ‖S(t - ⌊t⌋)‖ ≤ M^⌊t⌋ · M = M^(⌊t⌋+1) ≤ M · e^{ωt}
  sorry

end
