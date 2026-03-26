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
import HilleYosida.Bernstein
import HilleYosida.FourierPD
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

Ref: Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" Thm 4.1.13.
Verified correct by Gemini Deep Think (2026-03-23).

**Proof:** See `semigroupGroupBochner_proof` in `Future/BernsteinTheorem.lean`.
The proof decomposes into spatial Bochner (each time slice) + temporal
Laplace (BCR d=0 via `semigroup_pd_laplace` in `BCR_d0.lean`) + product
measure assembly. Modulo 4 classical analysis axioms (bump functions,
convolution smoothness, Fourier approximation of indicators, measure kernels). -/
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
  -- Proved in Future/BernsteinTheorem.lean as `semigroupGroupBochner_proof`.
  -- Cannot import here due to circular dependency (BernsteinTheorem imports this file).
  -- To verify: `lake build HilleYosida.Future.BernsteinTheorem` (0 sorrys).
  -- Restructuring imports to eliminate this sorry is a TODO.
  sorry

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
  · -- G is bounded: ‖G(t,a)‖ ≤ μ(univ)
    haveI := hfin
    have norm_exp_I : ∀ r : ℝ, ‖exp (Complex.I * ↑r)‖ = 1 := fun r => by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I r
    refine ⟨(μ Set.univ).toReal, fun t a => ?_⟩
    apply le_trans (norm_integral_le_integral_norm _)
    apply le_trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall (fun p => by
        dsimp; rw [norm_mul, norm_exp_I, norm_exp_I, mul_one])))
    simp [integral_const, Measure.real]
  · -- G is continuous via MeasureTheory.continuous_of_dominated
    haveI := hfin
    have norm_exp_I : ∀ r : ℝ, ‖exp (Complex.I * ↑r)‖ = 1 := fun r => by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I r
    exact MeasureTheory.continuous_of_dominated
      (F := fun (x : ℝ × (Fin d → ℝ)) p =>
        exp (Complex.I * ↑(x.1 * p.1)) * exp (Complex.I * ↑(∑ i, p.2 i * x.2 i)))
      (bound := fun _ => 1)
      (fun x => (Continuous.aestronglyMeasurable (by fun_prop)))
      (fun x => ae_of_all μ (fun p => by
        dsimp; rw [norm_mul, norm_exp_I, norm_exp_I, mul_one]))
      (integrable_const 1)
      (ae_of_all μ (fun p => by fun_prop))
  · -- G is PD on ℝ: ∑ c̄ᵢcⱼ G(tⱼ-tᵢ, aⱼ-aᵢ) = ∫ |∑ⱼ cⱼ exp(itⱼp+i⟨aⱼ,q⟩)|² dμ ≥ 0
    -- The double sum factors as ‖∑ⱼ cⱼ φⱼ(p)‖² which is real and nonneg.
    -- Then ∫ (nonneg real) dμ is nonneg real.
    intro n c ts as
    haveI := hfin
    have norm_exp_I : ∀ r : ℝ, ‖exp (Complex.I * ↑r)‖ = 1 := fun r => by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I r
    -- Define zⱼ(p) = cⱼ exp(I tⱼ p.1) exp(I ⟨aⱼ, p.2⟩)
    set z : Fin n → (ℝ × (Fin d → ℝ)) → ℂ :=
      fun j p => c j * exp (Complex.I * ↑(ts j * p.1)) *
        exp (Complex.I * ↑(∑ i, p.2 i * as j i))
    -- Key identity: ∑ᵢⱼ star(cᵢ) cⱼ exp(I(tⱼ-tᵢ)p) exp(I⟨aⱼ-aᵢ,q⟩)
    --   = ∑ᵢⱼ star(zᵢ(p)) zⱼ(p) = star(∑ z(p)) * (∑ z(p)) = ‖∑ z‖²
    -- Then q = ∫ ‖∑ z(p)‖² dμ, which has im=0 and re≥0.
    -- The swap of ∑ and ∫ uses linearity; the ∑ᵢⱼ factoring uses Finset.sum_mul_sum.
    -- Key algebra: ∑ᵢⱼ star(wᵢ) wⱼ = star(∑ w)(∑ w) for any w : Fin n → ℂ
    have sum_star_mul : ∀ (m : ℕ) (w : Fin m → ℂ),
        ∑ i, ∑ j, star (w i) * w j = star (∑ i, w i) * (∑ j, w j) := by
      intro m w
      have h1 : (∑ i, star (w i)) * (∑ j, w j) = ∑ i, ∑ j, star (w i) * w j := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [← h1, show (∑ i, star (w i)) = star (∑ i, w i) from
        (map_sum (starRingEnd ℂ) w Finset.univ).symm]
    -- And star(z) * z is real and nonneg for any z : ℂ
    have star_mul_self_nonneg : ∀ (w : ℂ), (star w * w).im = 0 ∧ 0 ≤ (star w * w).re := by
      intro w
      rw [show star w * w = ↑(Complex.normSq w) from Complex.normSq_eq_conj_mul_self.symm]
      exact ⟨Complex.ofReal_im _, Complex.ofReal_re _ ▸ Complex.normSq_nonneg w⟩
    -- Define χⱼ(p) = exp(I tⱼ p.1) exp(I ⟨aⱼ, p.2⟩)
    set χ : Fin n → (ℝ × (Fin d → ℝ)) → ℂ :=
      fun j p => exp (Complex.I * ↑(ts j * p.1)) *
        exp (Complex.I * ↑(∑ k, p.2 k * as j k))
    -- G(tⱼ-tᵢ, aⱼ-aᵢ) = ∫ star(χᵢ) χⱼ dμ by exp factoring
    have hG_eq : ∀ i j, G (ts j - ts i) (as j - as i) =
        ∫ p, star (χ i p) * χ j p ∂μ := by
      intro i j
      change ∫ p, exp (Complex.I * ↑((ts j - ts i) * p.1)) *
        exp (Complex.I * ↑(∑ k, p.2 k * (as j - as i) k)) ∂μ =
        ∫ p, star (χ i p) * χ j p ∂μ
      congr 1; ext p; simp only [χ]
      -- Helper: star of each exponential
      have hstar_exp : ∀ (r : ℝ), star (exp (Complex.I * ↑r)) =
          exp (-(Complex.I * ↑r)) := by
        intro r
        rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl,
            ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
            neg_mul]
      have hstar_χ : ∀ j, star (χ j p) =
          exp (-(Complex.I * ↑(ts j * p.1))) *
          exp (-(Complex.I * ↑(∑ k, p.2 k * as j k))) := by
        intro j; simp only [χ, star_mul]; rw [hstar_exp, hstar_exp]; ring
      rw [hstar_χ]
      simp only [← Complex.exp_add]
      -- Both sides are exp of a single exponent; show exponents equal
      congr 1; push_cast; simp only [Pi.sub_apply, Complex.ofReal_sub]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
    simp_rw [hG_eq]
    exact pd_quadratic_form_of_measure μ c χ (fun i j => by
      -- star(χ i) * χ j is integrable: bounded by 1 on finite measure
      apply (integrable_const (1 : ℂ)).mono
      · exact (Continuous.aestronglyMeasurable (by fun_prop))
      · exact ae_of_all μ (fun p => by
          simp only [χ, norm_mul, norm_star, norm_exp_I, mul_one, norm_one,
            le_refl]))

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
