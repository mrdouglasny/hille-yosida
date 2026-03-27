/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bimeasure Extension Theorem (Kingman-Carathéodory)

Given a family of finite measures σ(B) on X indexed by measurable
sets B ⊆ Y, where B ↦ σ(B)(A) is countably additive for each A,
there exists a joint measure μ on X × Y with μ(A × B) = σ(B)(A).

This is a consequence of the Carathéodory extension theorem applied
to the semiring of measurable rectangles.

## References

* Kingman (1967), "Completely random measures", Theorem 1
* Kallenberg, "Foundations of Modern Probability", §1.9
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Count

open MeasureTheory Measure Set

/-- **Bimeasure extension (Kingman-Carathéodory).**

Given a family of finite measures `σ(B)` on `X` indexed by measurable
sets `B ⊆ Y`, where `B ↦ σ(B)(A)` is countably additive for each
measurable `A`, there exists a finite measure `μ` on `X × Y` satisfying
`μ(A × B) = σ(B)(A)` on measurable rectangles.

**Proof route** (not formalized):
1. Define a premeasure on the semiring of measurable rectangles via
   `π(A × B) = σ(B)(A)`.
2. Verify σ-subadditivity of π using countable additivity in each variable
   and Fubini-Tonelli for the resulting iterated sums.
3. Apply Carathéodory's extension theorem (`OuterMeasure.toMeasure`) to
   obtain a measure on the product σ-algebra.
4. Verify `μ(A × B) = π(A × B) = σ(B)(A)` on rectangles. -/
axiom bimeasure_extension
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (σ : {B : Set Y // MeasurableSet B} → Measure X)
    (hfin : ∀ B, IsFiniteMeasure (σ B))
    (h_empty : σ ⟨∅, MeasurableSet.empty⟩ = 0)
    (h_iUnion : ∀ (B : ℕ → Set Y) (hB : ∀ n, MeasurableSet (B n))
      (hdisj : Pairwise (Function.onFun Disjoint B)),
      σ ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩ =
        Measure.sum (fun n => σ ⟨B n, hB n⟩)) :
    ∃ (μ : Measure (X × Y)),
      IsFiniteMeasure μ ∧
      ∀ (A : Set X) (hA : MeasurableSet A) (B : Set Y) (hB : MeasurableSet B),
        μ (A ×ˢ B) = σ ⟨B, hB⟩ A
