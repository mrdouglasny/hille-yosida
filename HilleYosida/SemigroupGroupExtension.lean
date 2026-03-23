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
      star (c i) * c j *
        F (ts i + ts j) (as j - as i)
    q.im = 0 ∧ 0 ≤ q.re

/-! ## Bochner Representation Theorem (BCR 4.1.13) -/

/-- **Semigroup-group Bochner theorem** (BCR Theorem 4.1.13).

Bounded continuous positive-definite functions on `[0,∞) × ℝ^d` are
Fourier-Laplace transforms of finite positive measures supported on
`[0,∞) × ℝ^d`:

  `F(t, a) = ∫ e^{-tp} e^{i⟨a, q⟩} dμ(p, q)`  for `t ≥ 0`

Ref: Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" Thm 4.1.13 -/
theorem semigroupGroupBochner (d : ℕ)
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
  -- BCR Theorem 4.1.13 (Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups", 1984).
  -- The proof uses Choquet's theorem on integral representations, the theory of
  -- completely monotone functions on abelian semigroups, and the Riesz representation
  -- theorem. This machinery is not available in Mathlib.
  -- Verified correct by Gemini Deep Think (2026-03-23).
  exact sorry

/-! ## Group Extension from Bochner Representation

Given the measure `μ` from `semigroupGroupBochner` (supported on `[0,∞) × ℝ^d`),
the group extension uses the **Fourier** (not Laplace) kernel:

  `G(t, a) = ∫ e^{itp} e^{i⟨a, q⟩} dμ(p, q)`  for all `t ∈ ℝ`

This converges for all `t ∈ ℝ` because `|e^{itp}| = 1` and `μ` is finite.
For `t ≥ 0`, analytic continuation from `e^{-tp}` to `e^{itp}` relates
`G` to `F` via the substitution `t ↦ -it`. -/

/-- The Fourier group function from the Bochner measure.

Given the measure `μ` from `semigroupGroupBochner` (supported on `[0,∞) × ℝ^d`),
define `G(t, a) = ∫ e^{itp} e^{i⟨a,q⟩} dμ(p,q)` for ALL `t ∈ ℝ`.

**`G` is NOT a pointwise extension of `F`**. They use different kernels:
- `F(t, a) = ∫ e^{-tp} e^{i⟨a,q⟩} dμ` (Laplace, defined for `t ≥ 0`)
- `G(t, a) = ∫ e^{itp} e^{i⟨a,q⟩} dμ` (Fourier, defined for all `t ∈ ℝ`)

They are related by analytic continuation in the time parameter, not by
equality. The "semigroup-to-group" extension means: the PD condition on
`[0,∞)` (semigroup) yields a measure whose Fourier transform `G` is
automatically PD on all of `ℝ` (group). This is the group-level Bochner
theorem: continuous PD functions on the group `(ℝ, +)` are exactly the
Fourier transforms of finite positive measures.

Note: `G(s+t, a) ≠ G(s, a) · G(t, a)` in general (product of integrals
≠ integral of product). The "group" structure is encoded in the PD condition
`Σ c̄ᵢ cⱼ G(tⱼ - tᵢ, aⱼ - aᵢ) ≥ 0` holding for all `t ∈ ℝ`. -/
theorem semigroupGroupBochnerExtension (d : ℕ)
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
      -- G is bounded (|e^{itp}| = 1 and μ is finite)
      (∃ C : ℝ, ∀ t a, ‖G t a‖ ≤ C) ∧
      -- G is continuous on all of ℝ × ℝ^d
      (Continuous (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2)) ∧
      -- G is positive-definite on all of ℝ (the group-level PD condition:
      -- the quadratic form is real and nonnegative, matching IsSemigroupGroupPD)
      (∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (as : Fin n → (Fin d → ℝ)),
        let q := ∑ i : Fin n, ∑ j : Fin n,
          star (c i) * c j * G (ts j - ts i) (as j - as i)
        q.im = 0 ∧ 0 ≤ q.re) := by
  -- Step 1: Get the measure from semigroupGroupBochner
  obtain ⟨μ, hfin, hsupp, hF⟩ := semigroupGroupBochner d F hcont hbdd hpd
  -- Step 2: Define G via the Fourier kernel
  set G : ℝ → (Fin d → ℝ) → ℂ := fun t a =>
    ∫ p : ℝ × (Fin d → ℝ),
      Complex.exp (Complex.I * ↑(t * p.1)) *
        Complex.exp (Complex.I * ↑(∑ i : Fin d, p.2 i * a i)) ∂μ
  refine ⟨μ, G, hfin, hsupp, hF, fun t a => rfl, ?_, ?_, ?_⟩
  · -- G is bounded: |e^{itp}| = 1 and μ is finite → ‖G(t,a)‖ ≤ μ(univ)
    sorry
  · -- G is continuous: dominated convergence (integrand bounded by 1, μ finite)
    sorry
  · -- G is PD on ℝ: ∑ c̄ᵢcⱼ G(tⱼ-tᵢ, aⱼ-aᵢ) = ∫ |∑ cⱼ e^{itⱼp+i⟨aⱼ,q⟩}|² dμ ≥ 0
    sorry

/-! ## Connection to QFT: Analytic Continuation to Unitary Group

The QFT application: given a contraction semigroup `S(t) = e^{-tH}` on a
**complex** Hilbert space with `H ≥ 0` (positive Hamiltonian), the spectral
theorem gives `S(t) = ∫ e^{-tλ} dE(λ)` where `E` is the spectral measure
supported on `[0, ∞)`. The **unitary** group is `U(t) = ∫ e^{itλ} dE(λ)`.

**Critical**: `S(t)` and `U(t)` are NOT the same operators. `S(t) = e^{-tH}`
is a contraction (dampens high frequencies), while `U(t) = e^{itH}` is unitary
(preserves norms). They are related by **analytic continuation** `t ↦ -it`,
NOT by equality. For unbounded `H` (any nontrivial QFT Hamiltonian), `S(t)`
is not invertible, so no bounded group `U` can satisfy `U(t) = S(t)` for
`t ≥ 0` with `U` also defined for `t < 0`.

The extension must happen on a **complex** Hilbert space, where the Wick
rotation `t ↦ -it` maps the real contraction semigroup to a unitary group.
This requires Stone's theorem (not yet in Mathlib) and the spectral theorem
for unbounded self-adjoint operators.

**Important**: The extension requires `H ≥ 0` (spectrum in `[0, ∞)`),
guaranteed by OS reflection positivity (E2). Without it, the heat semigroup
shows general contraction semigroups don't admit any such extension. -/

-- NOTE: The full complex-Hilbert-space version of this theorem requires:
-- 1. InnerProductSpace ℂ H (complex inner product)
-- 2. Unitary group U(t) : H →L[ℂ] H (complex-linear)
-- 3. Spectral theorem / Stone's theorem (not in Mathlib)
-- 4. The connection S(t) ↔ U(t) via analytic continuation, not pointwise equality
--
-- The contraction semigroup S(t) = e^{-tH} maps to the unitary group U(t) = e^{itH}
-- via the spectral measure: ⟨x, S(t)x⟩ = ∫ e^{-tλ} d⟨x, E(λ)x⟩ and
-- ⟨x, U(s)x⟩ = ∫ e^{isλ} d⟨x, E(λ)x⟩. These are NOT equal for real t = s;
-- they are related by analytic continuation t ↦ -it.
--
-- This is deferred until Stone's theorem and the spectral theorem for unbounded
-- self-adjoint operators are available in Mathlib.

end
