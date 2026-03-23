/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bernstein's Theorem and the BCR Decomposition

This file states Bernstein's theorem for completely monotone functions on
`[0, ∞)` and sketches how BCR Theorem 4.1.13 decomposes into:

  **BCR 4.1.13 = Bochner on ℝ^d  +  Bernstein on [0, ∞)**

The Bochner theorem on ℝ^d is fully proved in the companion project
`github.com/mrdouglasny/bochner` (0 sorries). Bernstein's theorem is
stated here as an axiom.

## Mathematical Content

### Bernstein's Theorem (1928)

A function `f : [0, ∞) → ℝ` is **completely monotone** if it is C^∞ and
`(-1)^n f^{(n)}(t) ≥ 0` for all `t > 0` and `n ∈ ℕ`. Equivalently
(Bernstein), `f` is completely monotone iff it is the Laplace transform
of a finite positive measure on `[0, ∞)`:

  `f(t) = ∫₀^∞ e^{-tp} dμ(p)`

### BCR Decomposition

Given a bounded continuous PD function `F(t, a)` on `[0, ∞) × ℝ^d`:

1. **Spatial Fourier part** (Bochner on ℝ^d): For each fixed `t ≥ 0`,
   `a ↦ F(t, a)` is PD on `(ℝ^d, +)`. By Bochner's theorem (proved in
   `mrdouglasny/bochner`), there exists a finite measure `ν_t` on `ℝ^d`
   with `F(t, a) = ∫ e^{i⟨a, q⟩} dν_t(q)`.

2. **Temporal Laplace part** (Bernstein on [0,∞)): The semigroup PD
   condition implies that for each Borel set `B ⊆ ℝ^d`, the function
   `t ↦ ν_t(B)` is completely monotone. By Bernstein's theorem, there
   exists a measure `σ_B` on `[0, ∞)` with
   `ν_t(B) = ∫₀^∞ e^{-tp} dσ_B(p)`.

3. **Product measure**: The family `{σ_B}` defines a measure `μ` on
   `[0, ∞) × ℝ^d` with `F(t, a) = ∫ e^{-tp} e^{i⟨a,q⟩} dμ(p, q)`.

## References

* Bernstein, "Sur les fonctions absolument monotones" (1928)
* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), §4.1
* Widder, "The Laplace Transform" (1941), Ch. IV
-/

import HilleYosida.SemigroupGroupExtension
import Bochner.Main

noncomputable section

open MeasureTheory

-- bochner_theorem and IsPositiveDefinite are now available from Bochner.Main

/-! ## Completely Monotone Functions -/

/-- A function `f : ℝ → ℝ` is completely monotone on `(0, ∞)` if it is
smooth and `(-1)^n f^{(n)}(t) ≥ 0` for all `t > 0` and `n ∈ ℕ`.

For the formal statement, we use the sequential characterization:
`f` is completely monotone iff for all `n ∈ ℕ`, `t > 0`, and `h > 0`,
the `n`-th forward difference `Δ_h^n f(t) := ∑ (-1)^k C(n,k) f(t + kh)`
satisfies `(-1)^n Δ_h^n f(t) ≥ 0`. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧
  ∀ (n : ℕ) (t : ℝ) (h : ℝ), 0 < t → 0 < h →
    0 ≤ (-1 : ℝ) ^ n * (Finset.sum (Finset.range (n + 1)) fun k =>
      (-1 : ℝ) ^ k * (n.choose k : ℝ) * f (t + k * h))

/-! ## Bernstein's Theorem -/

/-- **Bernstein's theorem** (1928).

A function `f : [0, ∞) → ℝ` is completely monotone if and only if it is
the Laplace transform of a finite positive measure on `[0, ∞)`:

  `f(t) = ∫₀^∞ e^{-tp} dμ(p)`  for all `t ≥ 0`.

The forward direction (Laplace transform is CM) is elementary. The
converse uses Widder's inversion formula or the Helly selection theorem
(compactness in the space of measures).

Ref: Bernstein (1928); Widder, "The Laplace Transform" Ch. IV;
[EN] implicit in the proof of Thm. II.3.5 via Yosida approximation. -/
axiom bernstein_theorem (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ (μ : Measure ℝ),
      IsFiniteMeasure μ ∧
      μ (Set.Iio 0) = 0 ∧
      ∀ (t : ℝ), 0 ≤ t →
        f t = ∫ p, Real.exp (-(t * p)) ∂μ

/-! ## BCR Decomposition: Step 1 — Spatial Bochner

For each fixed `t ≥ 0`, the function `a ↦ F(t, a)` is positive-definite
on the group `(ℝ^d, +)` in the sense of `IsPositiveDefinite` from the
bochner repo. This follows from `IsSemigroupGroupPD` by setting all
time parameters to `t/2`. -/

open Complex in
/-- For fixed `t ≥ 0`, the spatial slice `a ↦ F(t/2 + t/2, a - 0) = F(t, a)`
is positive-definite on `(ℝ^d, +)` in the sense of the bochner repo.

From `IsSemigroupGroupPD`: setting `ts_i = t/2` for all `i` gives
`∑ᵢⱼ c̄ᵢ cⱼ F(t, aⱼ - aᵢ) ≥ 0`, which is exactly `IsPositiveDefinite`
for the function `a ↦ F(t, a)` on the additive group `Fin d → ℝ`. -/
lemma spatial_slice_pd {d : ℕ} {F : ℝ → (Fin d → ℝ) → ℂ}
    (hpd : IsSemigroupGroupPD d F) (t : ℝ) (ht : 0 ≤ t) :
    IsPositiveDefinite (fun a => F t a) where
  hermitian := by
    intro a
    -- Step 1: F(t, 0) is real (PD with n=1, ts=[t/2])
    have h0 := (hpd 1 ![1] ![t / 2] ![0] (by intro i; fin_cases i; simp; linarith)).1
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, star_one, one_mul,
      sub_zero, show t / 2 + t / 2 = t from by ring] at h0
    -- h0 : (F t 0).im = 0
    -- Step 2: Im(F(t,a) + F(t,-a)) = 0 (PD with n=2, c=[1,1])
    have h1 := (hpd 2 ![1, 1] ![t / 2, t / 2] ![0, a]
      (by intro i; fin_cases i <;> simp <;> linarith)).1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, star_one, one_mul, sub_zero, zero_sub,
      show t / 2 + t / 2 = t from by ring] at h1
    -- Step 3: Re(F(t,a) - F(t,-a)) = 0 (PD with n=2, c=[1,I])
    have h2 := (hpd 2 ![1, Complex.I] ![t / 2, t / 2] ![0, a]
      (by intro i; fin_cases i <;> simp <;> linarith)).1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, star_one, one_mul, map_mul, starRingEnd_self_apply,
      sub_zero, zero_sub,
      show t / 2 + t / 2 = t from by ring] at h2
    -- h1 : im(... F t a ... F t (-a) ...) = 0
    -- h2 : im(... I * F t a ... star I * F t (-a) ...) = 0
    simp only [neg_zero, sub_self, Complex.star_def, Complex.conj_I,
      neg_mul, one_mul, neg_neg, Complex.I_mul_I] at h0 h1 h2
    -- h1: (F t 0 + F t a + (F t (-a) + F t 0)).im = 0
    -- h2: (F t 0 + I * F t a + (-I * F t (-a) + -F t 0)).im = 0 (after star I = -I)
    -- Check h1 type:
    -- Goal: F t (-a) = starRingEnd ℂ (F t a)
    -- h1: (F t 0 + F t a + (F t (-a) + F t 0)).im = 0
    -- h2: (F t 0 + I * F t a + (-I * F t (-a) + -F t 0)).im = 0
    -- These are rfl-reducible to linear combinations of Re/Im parts
    -- h0: (F t 0).im = 0
    -- h1: (F t 0 + F t a + (F t (-a) + F t 0)).im = 0
    -- h2: (F t 0 + I * F t a + (-I * F t (-a) + -F t 0)).im = 0
    -- Extract: Im(F(t,a) + F(t,-a)) = 0 from h0 + h1
    have him : (F t a).im + (F t (-a)).im = 0 := by
      have := h1; simp only [Complex.add_im] at this; linarith
    -- Extract: Re(F(t,a) - F(t,-a)) = 0 from h0 + h2
    -- (I * z).im = z.re, (-I * z).im = -z.re, (-z).im = -z.im
    have hre : (F t a).re - (F t (-a)).re = 0 := by
      have := h2
      simp only [Complex.add_im, Complex.mul_im, Complex.neg_im, Complex.neg_re,
        Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        mul_zero, mul_one, zero_mul, zero_add, add_zero] at this
      linarith
    apply Complex.ext
    · simp only [starRingEnd_self_apply, Complex.conj_re]; linarith
    · simp only [starRingEnd_self_apply, Complex.conj_im]; linarith
  nonneg := by
    intro m pts c
    -- Key trick: negate the spatial arguments! (-pts j) - (-pts i) = pts i - pts j
    have h := (hpd m c (fun _ => t / 2) (fun i => -pts i) (fun _ => by linarith)).2
    -- Rewrite inside sums: -ptsⱼ - (-ptsᵢ) = ptsᵢ - ptsⱼ and t/2+t/2 = t
    simp_rw [show ∀ i j : Fin m, -pts j - -pts i = pts i - pts j from
      fun _ _ => by abel, show t / 2 + t / 2 = t from by ring] at h
    exact h

/-! ## BCR Decomposition: Steps 2–7

The remaining steps to complete the BCR proof:

2. For each `t ≥ 0`, apply `bochner_theorem` to `spatial_slice_pd` to get
   a probability measure `ν_t` on `Fin d → ℝ` with
   `F(t, a) = ∫ e^{i⟨a, q⟩} dν_t(q)`.
   (Requires showing `F(t, ·)` is continuous and `F(t, 0) = 1`; the latter
   may need normalization.)

3. Show that for each Borel set `B ⊆ ℝ^d`, the function `t ↦ ν_t(B)` is
   completely monotone (from the semigroup PD condition on `F`).

4. Apply `bernstein_theorem` to each `t ↦ ν_t(B)` to get a measure
   `σ_B` on `[0, ∞)` with `ν_t(B) = ∫₀^∞ e^{-tp} dσ_B(p)`.

5. The family `{σ_B}` defines a product measure `μ` on `[0, ∞) × ℝ^d`.

6. Verify: `F(t, a) = ∫ e^{-tp} e^{i⟨a,q⟩} dμ(p, q)` by combining
   steps 2 and 4.

7. Show `μ` is a finite measure (from boundedness of `F`).
-/

end
