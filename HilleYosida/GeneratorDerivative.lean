/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Derivative of the Semigroup: d/dt S(t)x = A S(t)x = S(t) Ax

For a C₀-semigroup S(t) with generator A, and x ∈ dom(A):
- S(t)x ∈ dom(A) for all t ≥ 0
- d/dt S(t)x = A(S(t)x) = S(t)(Ax)

This is [EN] Proposition II.1.4(c) / [Linares] Proposition 5.

## Main results

- `semigroup_maps_domain` — S(t) maps dom(A) to dom(A)
- `semigroup_generator_comm` — S(t)(Ax) = A(S(t)x) for x ∈ dom(A)

## References

- Engel-Nagel, "One-Parameter Semigroups for Linear Evolution Equations",
  Proposition II.1.4
-/

import HilleYosida.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

open Filter

noncomputable section

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X)

/-- S(t) maps the domain of A into itself: if x ∈ dom(A) then S(t)x ∈ dom(A).

Proof: for x ∈ dom(A), the difference quotient
  (S(h)(S(t)x) - S(t)x)/h = S(t)((S(h)x - x)/h)
converges to S(t)(Ax) as h → 0⁺ (by continuity of S(t) and the
definition of Ax as the limit of (S(h)x - x)/h). -/
theorem semigroup_maps_domain (x : X) (hx : S.generator x)
    (t : ℝ) (ht : 0 ≤ t) :
    S.generator (S.operator t x) := by
  obtain ⟨Ax, hAx⟩ := hx
  refine ⟨S.operator t Ax, ?_⟩
  -- (S(h)(S(t)x) - S(t)x)/h = S(t)((S(h)x - x)/h) → S(t)(Ax)
  have heq : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0),
      (1/h) • (S.operator h (S.operator t x) - S.operator t x) =
      S.operator t ((1/h) • (S.operator h x - x)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh_pos : 0 < h := hh
    -- S(h)(S(t)x) = S(h+t)x = S(t)(S(h)x) by semigroup property
    have h_comm : S.operator h (S.operator t x) = S.operator t (S.operator h x) := by
      rw [← ContinuousLinearMap.comp_apply, ← S.semigroup h t (le_of_lt hh_pos) ht,
          add_comm,
          S.semigroup t h ht (le_of_lt hh_pos), ContinuousLinearMap.comp_apply]
    rw [h_comm, ← map_sub, ← map_smul]
  -- S(t) is continuous, so S(t)(limit) = limit of S(t)(·)
  exact (((S.operator t).continuous.tendsto _).comp hAx).congr' (heq.mono (fun _ h => h.symm))

/-- The generator commutes with the semigroup on dom(A):
A(S(t)x) = S(t)(Ax) for x ∈ dom(A).

This follows from semigroup_maps_domain: we showed the limit of
(S(h)(S(t)x) - S(t)x)/h is S(t)(Ax), so A(S(t)x) = S(t)(Ax). -/
theorem semigroup_generator_comm (x : X) (hx : S.generator x)
    (t : ℝ) (ht : 0 ≤ t) :
    let Ax := Classical.choose hx
    let AStx := Classical.choose (S.semigroup_maps_domain x hx t ht)
    AStx = S.operator t Ax := by
  -- Both are the unique limit of (S(h)(S(t)x) - S(t)x)/h
  -- semigroup_maps_domain showed this limit is S(t)(Ax)
  -- The generator value at S(t)x is by definition this limit
  set Ax := Classical.choose hx with hAx_def
  set AStx := Classical.choose (S.semigroup_maps_domain x hx t ht) with hAStx_def
  have hAx := Classical.choose_spec hx
  have hAStx := Classical.choose_spec (S.semigroup_maps_domain x hx t ht)
  -- Both AStx and S(t)(Ax) are limits of (S(h)(S(t)x) - S(t)x)/h
  have h_target : Tendsto (fun h => (1/h) • (S.operator h (S.operator t x) - S.operator t x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S.operator t Ax)) := by
    have heq : ∀ᶠ h in nhdsWithin 0 (Set.Ioi 0),
        (1/h) • (S.operator h (S.operator t x) - S.operator t x) =
        S.operator t ((1/h) • (S.operator h x - x)) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have h_comm : S.operator h (S.operator t x) = S.operator t (S.operator h x) := by
        rw [← ContinuousLinearMap.comp_apply, ← S.semigroup h t (le_of_lt hh) ht,
            add_comm, S.semigroup t h ht (le_of_lt hh), ContinuousLinearMap.comp_apply]
      rw [h_comm, ← map_sub, ← map_smul]
    exact (((S.operator t).continuous.tendsto _).comp hAx).congr' (heq.mono (fun _ h => h.symm))
  exact tendsto_nhds_unique hAStx h_target

end StronglyContinuousSemigroup

end
