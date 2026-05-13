/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Positive-Definite Functions on `[0,∞) × ℝ^d`

Shared definitions for the semigroup/group Bochner development.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open MeasureTheory Complex Set Filter

/-- A function on `[0,∞) × ℝ^d` is positive-definite with respect to the
involutive semigroup structure `(t, a)^* = (t, -a)`. -/
def IsSemigroupGroupPD (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (as : Fin n → (Fin d → ℝ)),
    (∀ i, 0 ≤ ts i) →
    let q := ∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        F (ts i + ts j) (as j - as i)
    q.im = 0 ∧ 0 ≤ q.re
