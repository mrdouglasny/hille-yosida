/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Semigroup-to-Group Extension via Bochner's Theorem

States and (ultimately) proves the Bochner representation theorem for
positive-definite functions on the involutive semigroup `[0,∞) × ℝ^d`,
and derives the semigroup-to-group extension for positive-generator semigroups.

## Mathematical Background

In Osterwalder-Schrader reconstruction, Euclidean time translations form a
contraction semigroup `e^{-tH}` (t ≥ 0), while Lorentzian time translations
form a unitary group `e^{itH}` (t ∈ ℝ). **Not every contraction semigroup
extends to a group** — the heat semigroup is a counterexample. The extension
requires a spectral positivity condition (H ≥ 0), guaranteed by OS reflection
positivity (E2).

The analytical bridge: the BCR Theorem 4.1.13 gives a Fourier-Laplace measure
representation for bounded continuous PD functions on `[0,∞) × ℝ^d`. The
measure μ is supported on `[0,∞) × ℝ^d`, and the Fourier integral
`G(t, a) = ∫ e^{itp} e^{i⟨a,q⟩} dμ(p,q)` extends the semigroup to all t ∈ ℝ.

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups", Theorem 4.1.13
* Reed-Simon II, §IX.8
* Osterwalder-Schrader I-II
-/

import HilleYosida.StronglyContinuousSemigroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open MeasureTheory Complex Set Filter

/-! ## Positive-Definite Functions on Involutive Semigroups -/

/-- A function on `[0,∞) × ℝ^d` is positive-definite with respect to the
involutive semigroup structure `(t, a)^* = (t, -a)`.

This is the condition arising from OS reflection positivity (E2). -/
def IsSemigroupGroupPD (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (as : Fin n → (Fin d → ℝ)),
    (∀ i, 0 ≤ ts i) →
    let q := ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j *
        F (ts i + ts j) (as j - as i)
    q.im = 0 ∧ 0 ≤ q.re

/-! ## Bochner Representation Theorem (BCR 4.1.13) -/

/-- **Semigroup-group Bochner theorem** (BCR Theorem 4.1.13).

Bounded continuous positive-definite functions on `[0,∞) × ℝ^d` are
Fourier-Laplace transforms of finite positive measures supported on
`[0,∞) × ℝ^d`:

  `F(t, a) = ∫ e^{-tp} e^{i⟨a, q⟩} dμ(p, q)`  for `t ≥ 0`

Ref: Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" Thm 4.1.13 -/
theorem semigroupGroup_bochner (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
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

/-! ## Group Extension from Bochner Representation

Given the measure `μ` from `semigroupGroup_bochner` (supported on `[0,∞) × ℝ^d`),
the group extension uses the **Fourier** (not Laplace) kernel:

  `G(t, a) = ∫ e^{itp} e^{i⟨a, q⟩} dμ(p, q)`  for all `t ∈ ℝ`

This converges for all `t ∈ ℝ` because `|e^{itp}| = 1` and `μ` is finite.
For `t ≥ 0`, analytic continuation from `e^{-tp}` to `e^{itp}` relates
`G` to `F` via the substitution `t ↦ -it`. -/

/-- The group extension from the Bochner measure representation.

Given a bounded continuous PD function `F` on `[0,∞) × ℝ^d` with Laplace
representation `F(t, a) = ∫ e^{-tp} e^{i⟨a,q⟩} dμ`, define the Fourier
group function `G(t, a) = ∫ e^{itp} e^{i⟨a,q⟩} dμ` for ALL `t ∈ ℝ`.

**`G` is NOT a pointwise extension of `F`**: `F(t, a) = ∫ e^{-tp} dμ` while
`G(t, a) = ∫ e^{itp} dμ`. They are related by analytic continuation (Wick
rotation) `t ↦ -it`, not by equality on `[0,∞)`. The connection is:
`F(t, a) = G(-it, a)` (as an analytic continuation in the time parameter).

Properties of `G`:
1. Fourier representation for all `t ∈ ℝ` (bounded since `|e^{itp}| = 1`)
2. Group law: `G(s+t, ·) = G(s, ·) * G(t, ·)` (pointwise, from exponential)
3. Continuity, boundedness, positive-definiteness on all of ℝ -/
theorem semigroupGroup_bochner_extension (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))) (G : ℝ → (Fin d → ℝ) → ℂ),
      IsFiniteMeasure μ ∧
      μ (Set.prod (Set.Iio 0) Set.univ) = 0 ∧
      -- F has Laplace representation (for t ≥ 0)
      (∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (-(↑(t * p.1) : ℂ)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ) ∧
      -- G has Fourier representation (for ALL t ∈ ℝ)
      (∀ (t : ℝ) (a : Fin d → ℝ),
        G t a = ∫ p : ℝ × (Fin d → ℝ),
          Complex.exp (Complex.I * ↑(t * p.1)) *
            Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ) ∧
      -- Group law (pointwise multiplicativity from exponential kernel)
      (∀ (s t : ℝ) (a : Fin d → ℝ),
        G (s + t) a = G s a * G t a) ∧
      -- G is bounded
      (∃ C : ℝ, ∀ t a, ‖G t a‖ ≤ C) ∧
      -- G is continuous
      (Continuous (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2)) ∧
      -- G is positive-definite on all of ℝ
      (∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (as : Fin n → (Fin d → ℝ)),
        0 ≤ (∑ i : Fin n, ∑ j : Fin n,
          starRingEnd ℂ (c i) * c j * G (ts j - ts i) (as j - as i)).re) := by
  sorry

/-! ## Connection to QFT: Semigroup Extension with Spectral Condition

The QFT application: given a contraction semigroup `S(t) = e^{-tH}` on a
**complex** Hilbert space with `H ≥ 0` (positive Hamiltonian), the spectral
theorem gives `S(t) = ∫ e^{-tλ} dE(λ)` where `E` is the spectral measure
supported on `[0, ∞)`. The **unitary** group is `U(t) = ∫ e^{itλ} dE(λ)`.

**Important**: This requires `H ≥ 0` (from OS reflection positivity E2).
Without it, the heat semigroup shows general contraction semigroups don't
extend to groups.

The full formalization needs Stone's theorem (not yet in Mathlib) and the
spectral theorem for unbounded self-adjoint operators. We state the result
on a real Hilbert space as a stepping stone; the complex version requires
additional infrastructure. -/

/-- Extension of a contraction semigroup on a real Hilbert space to a
strongly continuous group, under the PD hypothesis (positive generator).

This is the real-Hilbert-space version. The full QFT application uses a
complex Hilbert space with unitary operators, which requires additional
infrastructure (complex inner product space, unitary group). -/
theorem semigroup_extends_to_group_of_positive_generator
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : ContractingSemigroup H)
    (hpd : ∀ (n : ℕ) (c : Fin n → ℝ) (ts : Fin n → ℝ) (xs : Fin n → H),
      (∀ i, 0 ≤ ts i) →
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        c i * c j * @inner ℝ H _ (xs i) (S.operator (ts i + ts j) (xs j))) :
    ∃ (U : ℝ → H →L[ℝ] H),
      (∀ (t : ℝ), 0 ≤ t → U t = S.operator t) ∧
      (∀ (s t : ℝ), U (s + t) = (U s).comp (U t)) ∧
      (∀ (x : H), Continuous (fun t => U t x)) := by
  sorry

end
