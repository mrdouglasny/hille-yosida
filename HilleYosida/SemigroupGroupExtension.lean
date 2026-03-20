/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Semigroup-to-Group Extension via Bochner's Theorem

This file states and (ultimately) proves the Bochner representation theorem
for positive-definite functions on the involutive semigroup `[0,∞) × ℝ^d`,
and derives the semigroup-to-group extension for positive-generator semigroups.

## Mathematical Background

In the Osterwalder-Schrader reconstruction of QFT:
- Euclidean time translations form a contraction semigroup `e^{-tH}` for `t ≥ 0`
- Lorentzian (Wightman) time translations form a unitary group `e^{itH}` for `t ∈ ℝ`

**Not every contraction semigroup extends to a group.** The heat semigroup
`e^{tΔ}` is a standard counterexample — it is a contraction semigroup that
is not invertible for `t < 0`. The extension requires an additional
hypothesis: the semigroup arises from a **positive-definite** function
(equivalently, the generator `H` has nonnegative spectrum, which is
guaranteed by OS reflection positivity E2).

## Main Results

* `semigroupGroup_bochner` — BCR Theorem 4.1.13: bounded continuous PD functions
  on `[0,∞) × ℝ^d` are Fourier-Laplace transforms. The measure representation
  immediately gives the extension to all `t ∈ ℝ`.
* `semigroupGroup_bochner_extension` — the group extension derived from the
  Bochner representation

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups", Theorem 4.1.13
* Reed-Simon II, §IX.8 (Fourier-Laplace representation)
* Osterwalder-Schrader I-II (application to QFT reconstruction)
-/

import HilleYosida.StronglyContinuousSemigroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open MeasureTheory Complex Set Filter

/-! ## Positive-Definite Functions on Involutive Semigroups -/

/-- A function on `[0,∞) × ℝ^d` is positive-definite with respect to the
involutive semigroup structure `(t, a)^* = (t, -a)`.

This is the exact condition arising from OS reflection positivity (E2):
the two-point function `⟨Ω, e^{-(s+t)H} e^{i⟨a-b, P⟩} Ω⟩` is PD in
the semigroup variables `(s, a), (t, b)` with the involution. -/
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

Note: `F` is only assumed to be defined and PD for `t ≥ 0`. The hypotheses
`hcont` and `hbdd` are on the restriction to `[0, ∞) × ℝ^d`.

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

Once the measure `μ` is obtained from `semigroupGroup_bochner`, the extension
to all `t ∈ ℝ` is immediate: the integral
  `G(t, a) = ∫ e^{-tp} e^{i⟨a, q⟩} dμ(p, q)`
converges for ALL `t ∈ ℝ` (not just `t ≥ 0`) because `μ` is supported on
`{p ≥ 0} × ℝ^d`, so the exponential `e^{-tp}` is bounded for `t < 0` too
(since `p ≥ 0` and `t < 0` give `e^{-tp} = e^{|t|p}`, but `μ` is finite
so the integral converges by dominated convergence with the bound from `hbdd`).

Actually: for `t < 0` and `p ≥ 0`, `e^{-tp} = e^{|t|p}` grows, so the integral
may diverge. The correct statement uses `e^{itp}` (Fourier, not Laplace) for the
group extension, which is bounded. The group is:
  `G(t, a) = ∫ e^{itp} e^{i⟨a, q⟩} dμ(p, q)` for all `t ∈ ℝ`

This requires the analytic continuation `t ↦ e^{-zp}` where `z = t` (real,
nonneg) is continued to `z = -it` (purely imaginary). -/

/-- The group extension: given the Bochner measure from `semigroupGroup_bochner`,
define `G(t, a)` for ALL `t ∈ ℝ` via the Fourier representation. -/
theorem semigroupGroup_bochner_extension (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2) (Set.Ici 0 ×ˢ Set.univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (G : ℝ → (Fin d → ℝ) → ℂ),
      -- G extends F on [0, ∞)
      (∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t → G t a = F t a) ∧
      -- G is continuous on all of ℝ × ℝ^d
      (Continuous (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2)) ∧
      -- G is bounded on all of ℝ × ℝ^d
      (∃ C : ℝ, ∀ t a, ‖G t a‖ ≤ C) := by
  sorry

/-! ## Connection to QFT: Semigroup Extension with Spectral Condition

The QFT application is more specific than the general Bochner theorem.
Given a contraction semigroup `S(t) = e^{-tH}` with `H ≥ 0` (positive
generator), the spectral theorem gives `S(t) = ∫ e^{-tλ} dE(λ)` where
`E` is the spectral measure of `H` supported on `[0, ∞)`. The unitary
group is then `U(t) = ∫ e^{itλ} dE(λ)`.

**Important**: This extension requires `H ≥ 0` (spectrum in `[0, ∞)`),
which comes from OS reflection positivity (E2). Without positivity,
the heat semigroup shows that general contraction semigroups do NOT
extend to groups.

The spectral-theoretic proof requires Stone's theorem (not yet in Mathlib),
so we state this as a separate theorem with the spectral hypothesis. -/

/-- Extension of a contraction semigroup to a unitary group, under the
additional hypothesis that the generator has nonneg spectrum (H ≥ 0).

This is the specific result needed for OS reconstruction: the Euclidean
semigroup `e^{-tH}` extends to the Lorentzian group `e^{itH}`.

Requires: spectral theory / Stone's theorem (not yet in Mathlib). -/
theorem semigroup_extends_to_group_of_positive_generator
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : ContractingSemigroup H)
    -- The additional spectral hypothesis: S is a PD semigroup
    -- (arises from reflection positivity in the OS context)
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
