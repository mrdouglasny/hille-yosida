/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Semigroup-to-Group Extension via Bochner's Theorem

This file proves that a one-parameter semigroup of bounded analytic functions
on a tube domain, satisfying Bochner-type polynomial-exponential growth bounds,
extends to a full one-parameter group.

## Mathematical Background

In the Osterwalder-Schrader reconstruction of QFT:
- Euclidean time translations form a contraction semigroup `e^{-tH}` for `t ≥ 0`
- Lorentzian (Wightman) time translations form a unitary group `e^{itH}` for `t ∈ ℝ`

The extension from semigroup to group is the analytical bridge between these
frameworks. The key input is that the semigroup consists of holomorphic functions
on a tube domain with controlled polynomial/exponential growth — this constrains
the spectrum of the generator H sufficiently to permit analytic continuation
from `t > 0` to all `t ∈ ℝ`.

## Main Results

* `semigroupGroup_bochner` — the extension theorem (axiom from OSreconstruction,
  to be proved)
* `semigroup_group_pd_extension` — the positive-definite version using the
  Fourier-Laplace representation from Berg-Christensen-Ressel

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups", Theorem 4.1.13
* Reed-Simon II, §IX.8 (Fourier-Laplace representation)
* Osterwalder-Schrader I-II (application to QFT reconstruction)
-/

import HilleYosida.StronglyContinuousSemigroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory Complex Set Filter

/-! ## The Semigroup-Group Bochner Axiom from OSreconstruction

This is copied from `OSReconstruction/SCV/SemigroupGroupBochner.lean` and will be
proved in this project. The statement:

Given a family `F(t, z)` of holomorphic functions on a tube domain that:
1. Forms a multiplicative semigroup in `t > 0`: `F(s+t, z) = F(s, z) · F(t, z)`
2. Satisfies polynomial-exponential growth: `‖F(t, z)‖ ≤ C · (1+‖z‖)^N · e^{-t}`

Then `F` extends to a group `G(t, z)` defined for ALL `t ∈ ℝ`, with:
1. `G(t, z) = F(t, z)` for `t > 0`
2. `G(t, ·)` is entire (holomorphic on all of ℂ^d) for each `t`
3. `G(s+t, z) = G(s, z) · G(t, z)` for all `s, t ∈ ℝ`
-/

/-! ## Positive-Definite Version (BCR Theorem 4.1.13) -/

/-- A function on `[0,∞) × ℝ^d` is positive-definite with respect to the
involutive semigroup structure `(t, a)^* = (t, -a)`. -/
def IsSemigroupGroupPD (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (as : Fin n → (Fin d → ℝ)),
    (∀ i, 0 ≤ ts i) →
    let q := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j *
        F (ts i + ts j) (as j - as i)
    q.im = 0 ∧ 0 ≤ q.re

/-- **Semigroup-group Bochner theorem** (BCR Theorem 4.1.13).

Bounded continuous positive-definite functions on `[0,∞) × ℝ^d` are
Fourier-Laplace transforms of finite positive measures supported on
`[0,∞) × ℝ^d`.

**Proof strategy**:
1. The semigroup PD condition implies the Fourier-Laplace representation
   `F(t, a) = ∫ e^{-tp} e^{i⟨a, q⟩} dμ(p, q)` for a finite positive measure μ
   supported on `[0,∞) × ℝ^d` (BCR Thm 4.1.13).
2. The representation immediately gives the group extension:
   `G(t, a) = ∫ e^{-tp} e^{i⟨a, q⟩} dμ(p, q)` for ALL `t ∈ ℝ`.
3. The semigroup property follows from the multiplicativity of exponentials
   under the same measure.

Ref: Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" Thm 4.1.13;
Reed-Simon II §IX.8 -/
theorem semigroupGroup_bochner (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : Continuous (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2))
    (hbdd : ∃ C : ℝ, ∀ t a, ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ := by
  sorry

/-! ## Hille-Yosida Semigroup-to-Group Extension

The QFT application: given a contraction semigroup `S(t) = e^{-tH}` for `t > 0`
with H ≥ 0 (positive Hamiltonian), the Fourier-Laplace representation from the
Bochner theorem constructs the unitary group `U(t) = e^{itH}` for all `t ∈ ℝ`.

The connection to the axiom system:
- The Euclidean semigroup comes from OS axiom E0 (temperedness)
- The positivity condition comes from OS axiom E2 (reflection positivity)
- The extension gives the Wightman unitary time evolution (axiom R6) -/

/-- From a contraction semigroup with positive generator to a unitary group.
The semigroup `e^{-tH}` for `t > 0` extends to `e^{itH}` for `t ∈ ℝ`
via the spectral representation. -/
theorem semigroup_extends_to_group
    (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (S : ContractingSemigroup X) :
    -- There exists a strongly continuous group extending the semigroup
    ∃ (U : ℝ → X →L[ℝ] X),
      -- U extends S: U(t) = S(t) for t ≥ 0
      (∀ (t : ℝ), 0 ≤ t → U t = S.operator t) ∧
      -- Group property: U(s + t) = U(s) ∘ U(t) for all s, t ∈ ℝ
      (∀ (s t : ℝ), U (s + t) = (U s).comp (U t)) ∧
      -- Strong continuity: t ↦ U(t)x is continuous for each x
      (∀ (x : X), Continuous (fun t => U t x)) := by
  sorry

end
