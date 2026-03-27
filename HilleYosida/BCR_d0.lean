/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# BCR Theorem 4.1.13 for d=0: PD on semigroup [0,∞) → Laplace transform

A bounded continuous function `f : [0,∞) → ℝ` satisfying the semigroup
positive-definite condition
  `∑ᵢⱼ c̄ᵢ cⱼ f(tᵢ+tⱼ) ≥ 0`
for all `tᵢ ≥ 0`, `cᵢ ∈ ℂ`, is the Laplace transform of a finite
positive measure on `[0,∞)`.

Proof route:
  PD →(forward differences)→ CM-discrete →(smoothness)→ CM →(Bernstein)→ Laplace

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), §4.2
* Widder, "The Laplace Transform" (1941), Ch. IV
-/

import HilleYosida.Bernstein
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Choose.Vandermonde

noncomputable section

open MeasureTheory Complex Finset Set
open scoped Convolution

/-! ## Semigroup PD condition for scalar functions -/

/-- PD on the additive semigroup [0,∞): `∑ c̄ᵢ cⱼ f(tᵢ+tⱼ) ≥ 0` for all
finite systems of points `tᵢ ≥ 0` and coefficients `cᵢ ∈ ℂ`. -/
def IsSemigroupPD (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ),
    (∀ i, 0 ≤ ts i) →
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j * (f (ts i + ts j) : ℂ)).re

/-! ## Basic properties of semigroup PD functions -/

/-- `f(0) ≥ 0` (n=1, c=[1], t=[0]). -/
lemma IsSemigroupPD.nonneg_zero (hpd : IsSemigroupPD f) : 0 ≤ f 0 := by
  have h := hpd 1 ![1] ![0] (by intro i; fin_cases i; simp)
  simp only [Fin.sum_univ_one, star_one, one_mul, add_zero,
    Matrix.cons_val_zero, Complex.ofReal_re] at h
  exact_mod_cast h

/-- `f(t) ≥ 0` for all `t ≥ 0` (from PD with n=1, c=[1], ts=[t/2]). -/
lemma IsSemigroupPD.nonneg (hpd : IsSemigroupPD f) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  -- PD with n=1, c=[1], ts=[t/2]: 0 ≤ |1|² f(t/2 + t/2) = f(t)
  have h := hpd 1 ![1] ![t / 2] (by intro i; fin_cases i; simp; linarith)
  simp only [Fin.sum_univ_one, add_halves, star_one, one_mul,
    Matrix.cons_val_zero, Complex.ofReal_re] at h
  exact_mod_cast h

/-- Subadditivity: `f(s) ≤ (f(0) + f(2*s))/2` from PD with c=[1,-1], ts=[0,s]. -/
lemma IsSemigroupPD.midpoint_ineq (hpd : IsSemigroupPD f) (s : ℝ) (hs : 0 ≤ s) :
    f s ≤ (f 0 + f (2 * s)) / 2 := by
  -- Compute the PD inequality directly in ℝ
  -- The PD condition with n=2, c=[1,-1], ts=[0,s] gives:
  -- 0 ≤ Re(conj(1)·1·f(0) + conj(1)·(-1)·f(s) + conj(-1)·1·f(s) + conj(-1)·(-1)·f(s+s))
  -- = Re(f(0) - f(s) - f(s) + f(s+s))  =  f(0) - 2f(s) + f(s+s)
  -- Since all f values are real, this is just a real number.
  have h_real : ((↑(f 0) - ↑(f s) - ↑(f s) + ↑(f (s + s)) : ℂ)).re =
    f 0 - f s - f s + f (s + s) := by
    simp [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  -- Show the PD sum equals this
  have hpd_val : 0 ≤ f 0 - f s - f s + f (s + s) := by
    rw [← h_real]
    have hpd2 := hpd 2 ![(1 : ℂ), -1] ![0, s] (by intro i; fin_cases i <;> simp [hs])
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hpd2
    convert hpd2 using 1
    simp [star_one, star_neg]
    ring
  have h2s : f (s + s) = f (2 * s) := by ring_nf
  linarith

/-- `|f(t)| ≤ f(0)` for bounded semigroup-PD functions.

The proof iterates the midpoint inequality `f(s) ≤ (f(0) + f(2s))/2` to get
`f(t) ≤ f(0) + (C - f(0))/2^n`, then takes `n → ∞`. -/
lemma IsSemigroupPD.abs_le (hpd : IsSemigroupPD f) (t : ℝ) (ht : 0 ≤ t)
    (hbdd : ∃ C : ℝ, ∀ s, 0 ≤ s → |f s| ≤ C) :
    |f t| ≤ f 0 := by
  obtain ⟨C, hC⟩ := hbdd
  -- f is nonneg, so |f(t)| = f(t)
  have hfnonneg : ∀ s, 0 ≤ s → 0 ≤ f s := fun s hs => hpd.nonneg s hs
  rw [abs_of_nonneg (hfnonneg t ht)]
  -- The bound C can be assumed ≥ 0
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 le_rfl)
  -- Key claim: for all n, f(t) ≤ f(0) + (C - f(0)) / 2^n
  -- We prove this by showing: for all n, f(t) ≤ (1 - 1/2^n) * f(0) + C / 2^n
  -- which is the same since (1 - 1/2^n) * f(0) + C/2^n = f(0) + (C - f(0))/2^n
  -- f(0) ≤ C (from the bound)
  have hf0C : f 0 ≤ C := by
    have := hC 0 le_rfl
    rwa [abs_of_nonneg (hfnonneg 0 le_rfl)] at this
  suffices hiter : ∀ n : ℕ, f t ≤ f 0 + (C - f 0) / 2 ^ n by
    -- Since (C - f(0))/2^n → 0, f(t) ≤ f(0)
    apply le_of_forall_pos_lt_add
    intro ε hε
    -- Find n such that (C - f 0) / 2^n < ε
    have hD : 0 ≤ C - f 0 := by linarith
    by_cases hD0 : C - f 0 = 0
    · linarith [hiter 0]
    · have hDpos : 0 < C - f 0 := lt_of_le_of_ne hD (Ne.symm hD0)
      -- Find n such that (1/2)^n < ε/(C - f 0), hence (C-f0)/2^n < ε
      have h12 : (1 : ℝ) / 2 < 1 := by norm_num
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hDpos) h12
      have h2n : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num : (0 : ℝ) < 2) n
      have hlt : (C - f 0) / 2 ^ n < ε := by
        -- hn : (1/2)^n < ε/(C-f0)
        -- Multiply both sides by (C - f 0):
        -- (C - f 0) * (1/2)^n < ε
        have := mul_lt_mul_of_pos_left hn hDpos
        rw [mul_div_cancel₀ _ (ne_of_gt hDpos)] at this
        -- this : (C - f 0) * (1/2)^n < ε ... hmm, need to relate to /2^n
        rw [div_lt_iff₀ h2n]
        calc C - f 0 = (C - f 0) * 1 := (mul_one _).symm
          _ ≤ (C - f 0) * ((1 / 2) ^ n * (2 ^ n)) := by
              apply mul_le_mul_of_nonneg_left _ hD
              rw [one_div, inv_pow, inv_mul_cancel₀ (ne_of_gt h2n)]
          _ = (C - f 0) * (1 / 2) ^ n * 2 ^ n := by ring
          _ < ε * 2 ^ n := by nlinarith
      linarith [hiter n]
  -- First prove a stronger claim by induction on the dyadic subdivision:
  -- ∀ m, f(t) ≤ (1 - 1/2^m) * f(0) + f(2^m * t) / 2^m
  have hdyadic : ∀ m : ℕ,
      f t ≤ (1 - 1 / (2 : ℝ) ^ m) * f 0 +
        f ((2 : ℝ) ^ m * t) / (2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      -- midpoint ineq at s = 2^m * t: f(2^m * t) ≤ (f(0) + f(2^{m+1} * t))/2
      have hpos : 0 ≤ (2 : ℝ) ^ m * t := mul_nonneg (pow_nonneg (by norm_num) m) ht
      have hmid := hpd.midpoint_ineq ((2 : ℝ) ^ m * t) hpos
      -- 2 * (2^m * t) = 2^{m+1} * t
      have h2m : 2 * ((2 : ℝ) ^ m * t) = (2 : ℝ) ^ (m + 1) * t := by
        rw [pow_succ]; ring
      rw [h2m] at hmid
      -- From ihm and hmid:
      -- f(t) ≤ (1 - 1/2^m) * f(0) + f(2^m * t) / 2^m
      --      ≤ (1 - 1/2^m) * f(0) + (f(0) + f(2^{m+1}*t)) / (2 * 2^m)
      --      = (1 - 1/2^{m+1}) * f(0) + f(2^{m+1}*t) / 2^{m+1}
      have h2m_pos : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) m
      have h2m1_pos : (0 : ℝ) < 2 ^ (m + 1) := pow_pos (by norm_num) (m + 1)
      calc f t ≤ (1 - 1 / (2 : ℝ) ^ m) * f 0 + f ((2 : ℝ) ^ m * t) / (2 : ℝ) ^ m := ihm
        _ ≤ (1 - 1 / (2 : ℝ) ^ m) * f 0 +
            ((f 0 + f ((2 : ℝ) ^ (m + 1) * t)) / 2) / (2 : ℝ) ^ m := by
            linarith [div_le_div_of_nonneg_right hmid h2m_pos.le]
        _ = (1 - 1 / (2 : ℝ) ^ (m + 1)) * f 0 +
            f ((2 : ℝ) ^ (m + 1) * t) / (2 : ℝ) ^ (m + 1) := by
            rw [pow_succ]; field_simp; ring
  -- Now use f(2^n * t) ≤ C to get f(t) ≤ f(0) + (C - f(0))/2^n
  intro n
  have h2n_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  have hfC : f ((2 : ℝ) ^ n * t) ≤ C := by
    have hpos : 0 ≤ (2 : ℝ) ^ n * t := mul_nonneg (pow_nonneg (by norm_num) n) ht
    have := hC _ hpos
    rwa [abs_of_nonneg (hfnonneg _ hpos)] at this
  have := hdyadic n
  -- (1 - 1/2^n) * f(0) + f(2^n*t)/2^n ≤ (1 - 1/2^n) * f(0) + C/2^n = f(0) + (C-f(0))/2^n
  have : f ((2 : ℝ) ^ n * t) / (2 : ℝ) ^ n ≤ C / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right hfC h2n_pos.le
  -- f(0) + (C - f(0))/2^n = (1 - 1/2^n) * f(0) + C/2^n
  have key : f 0 + (C - f 0) / (2 : ℝ) ^ n = (1 - 1 / (2 : ℝ) ^ n) * f 0 + C / (2 : ℝ) ^ n := by
    field_simp; ring
  linarith

/-! ## Forward differences and the CM-discrete condition

The key insight: the PD condition with specific test vectors gives
`(-1)^n Δ_h^n f(t) ≥ 0` where `Δ_h` is the forward difference operator.

This is the discrete/finite-difference version of complete monotonicity. -/

/-- Forward difference operator: `Δ_h f(t) = f(t+h) - f(t)`. -/
def forwardDiff (h : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (t + h) - f t

/-- Iterated forward difference: `Δ_h^n f(t) = ∑_{k=0}^n (-1)^{n-k} C(n,k) f(t+kh)`. -/
def iterForwardDiff : ℕ → ℝ → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, f, t => f t
  | n+1, h, f, t => iterForwardDiff n h (forwardDiff h f) t

/-- Helper: `iterForwardDiff` satisfies the first-order recursion
    `Δ^{n+1}_h f(t) = Δ^n_h f(t+h) - Δ^n_h f(t)`. -/
lemma iterForwardDiff_succ_eq (n : ℕ) (h : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    iterForwardDiff (n + 1) h f t =
    iterForwardDiff n h f (t + h) - iterForwardDiff n h f t := by
  induction n generalizing f t with
  | zero => simp [iterForwardDiff, forwardDiff]
  | succ n ih =>
    -- By def: Δ^{n+2} = Δ^{n+1} ∘ Δ_h, by IH: Δ^{n+1} g = Δ^n g(·+h) - Δ^n g
    -- By def: iterForwardDiff n h (forwardDiff h f) x = iterForwardDiff (n+1) h f x
    change iterForwardDiff (n + 1) h (forwardDiff h f) t =
      iterForwardDiff (n + 1) h f (t + h) - iterForwardDiff (n + 1) h f t
    rw [ih (forwardDiff h f) t]
    -- Goal: iterForwardDiff n h (forwardDiff h f) (t+h) - iterForwardDiff n h (forwardDiff h f) t
    --     = iterForwardDiff (n+1) h f (t+h) - iterForwardDiff (n+1) h f t
    -- Both sides match by def of iterForwardDiff
    rfl

/-- Shifting a sum: `∑_{k=0}^{n} a(k) * g(k+1) = ∑_{k=0}^{n+1} a(k-1) * g(k)`
where `a(-1) = 0` (using natural subtraction). -/
private lemma sum_shift_index (n : ℕ) (a : ℕ → ℝ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), a k * g (k + 1) =
    ∑ k ∈ Finset.range (n + 2), (if k = 0 then 0 else a (k - 1)) * g k := by
  -- sum_range_succ' : ∑ k in range(n+2), f k = (∑ k in range(n+1), f(k+1)) + f 0
  symm
  rw [Finset.sum_range_succ']
  -- The k=0 term simplifies to 0
  simp only [ite_true, zero_mul, add_zero]
  -- The shifted terms: (if k+1=0 then 0 else a((k+1)-1)) * g(k+1) = a k * g(k+1)
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [show k + 1 ≠ 0 from Nat.succ_ne_zero k, ite_false, Nat.add_sub_cancel]

/-- Extending a sum by one term with zero padding. -/
private lemma sum_extend_range (n : ℕ) (a : ℕ → ℝ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), a k * g k =
    ∑ k ∈ Finset.range (n + 2), (if k = n + 1 then 0 else a k) * g k := by
  symm
  rw [Finset.sum_range_succ]
  simp only [ite_true, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≠ n + 1 := by
    have := Finset.mem_range.mp hk
    omega
  rw [if_neg hk']

private lemma forwardDiff_sum_recurrence (n : ℕ) (g : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * g (k + 1)) -
    (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * g k) =
    ∑ k ∈ Finset.range (n + 2),
      (-1 : ℝ) ^ (n + 1 - k) * ((n + 1).choose k : ℝ) * g k := by
  -- Rewrite the first sum as a sum over range(n+2) with shifted index
  rw [show (fun k => (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * g (k + 1)) =
    (fun k => ((-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) * g (k + 1)) from rfl]
  rw [sum_shift_index n (fun k => (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) g]
  -- Rewrite the second sum as a sum over range(n+2) with zero padding
  rw [show (fun k => (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * g k) =
    (fun k => ((-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) * g k) from rfl]
  rw [sum_extend_range n (fun k => (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) g]
  -- Now both LHS sums are over range(n+2). Combine into single sum.
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← sub_mul]
  congr 1
  have hk' : k < n + 2 := Finset.mem_range.mp hk
  -- Case split: k = 0, 1 ≤ k ≤ n, k = n+1
  by_cases hk0 : k = 0
  · -- k = 0: LHS = 0 - (-1)^n * C(n,0) = -(-1)^n = (-1)^{n+1}
    subst hk0
    simp [Nat.choose_zero_right]
    ring
  · by_cases hkn1 : k = n + 1
    · -- k = n+1: LHS = (-1)^0 * C(n,n) - 0 = 1
      subst hkn1
      simp [Nat.choose_self]
    · -- 1 ≤ k ≤ n: use Pascal's identity
      have hkle : k ≤ n := by omega
      simp only [if_neg hk0, if_neg hkn1]
      -- Goal: (-1)^{n-(k-1)} * C(n,k-1) - (-1)^{n-k} * C(n,k) = (-1)^{n+1-k} * C(n+1,k)
      -- Step 1: n - (k-1) = (n-k) + 1
      have hsign : n - (k - 1) = n - k + 1 := by omega
      rw [hsign, pow_succ]
      -- Now LHS = (-1)^{n-k} * (-1) * C(n,k-1) - (-1)^{n-k} * C(n,k)
      --         = (-1)^{n-k} * (-C(n,k-1) - C(n,k))
      -- Step 2: (-1)^{n+1-k} = (-1)^{n-k} * (-1)
      have hsign2 : n + 1 - k = (n - k) + 1 := by omega
      rw [hsign2, pow_succ]
      -- Step 3: Pascal's identity
      have hpascal : (n + 1).choose k = n.choose (k - 1) + n.choose k := by
        have hk1 : k = (k - 1) + 1 := by omega
        rw [hk1]; exact (Nat.choose_succ_succ' n (k - 1)).symm
      push_cast [hpascal]
      ring

/-- Explicit formula: `Δ_h^n f(t) = ∑_{k=0}^n (-1)^{n-k} C(n,k) f(t+kh)`. -/
lemma iterForwardDiff_eq_sum (n : ℕ) (h : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    iterForwardDiff n h f t =
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * f (t + k * h) := by
  induction n generalizing f t with
  | zero => simp [iterForwardDiff]
  | succ n ih =>
    rw [iterForwardDiff_succ_eq, ih, ih]
    -- LHS: ∑ k, (-1)^(n-k) C(n,k) f(t+h+k*h) - ∑ k, (-1)^(n-k) C(n,k) f(t+k*h)
    -- We need f(t+h+k*h) = f(t+(k+1)*h)
    have key : ∀ (k : ℕ), f (t + h + ↑k * h) = (fun j => f (t + ↑j * h)) (k + 1) := by
      intro k; congr 1; ring
    simp_rw [key]
    -- Goal should now match forwardDiff_sum_recurrence
    have := forwardDiff_sum_recurrence n (fun k => f (t + ↑k * h))
    convert this using 1
    · (congr 1; apply Finset.sum_congr rfl; intro k _; push_cast; ring)

/-- The Vandermonde convolution identity for signed binomial coefficients:
`∑_i ∑_j (-1)^{i+j} C(m,i) C(m,j) g(i+j) = ∑_p (-1)^p C(2m,p) g(p)`.

Follows from `Nat.add_choose_eq`: `(m+m).choose k = ∑_{i+j=k} C(m,i) C(m,j)`. -/
private lemma vandermonde_convolution_sum (m : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ (i + j) * (m.choose i : ℝ) * (m.choose j : ℝ) * g (i + j) =
    ∑ p ∈ Finset.range (2 * m + 1),
      (-1 : ℝ) ^ p * ((2 * m).choose p : ℝ) * g p := by
  -- Step 1: Convert LHS double sum to sum over product set
  rw [← Finset.sum_product']
  -- Step 2: Regroup by p = i + j using sum_fiberwise_of_maps_to
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ij : ℕ × ℕ => ij.1 + ij.2)
    (t := Finset.range (2 * m + 1)) (by
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_product, Finset.mem_range] at hij ⊢; omega)]
  -- LHS = ∑ p ∈ range(2m+1), ∑ (i,j) ∈ filter(i+j=p), (-1)^(i+j) * C(m,i) * C(m,j) * g(i+j)
  apply Finset.sum_congr rfl
  intro p _
  -- Simplify each term using filter condition i+j = p
  have hsub : ∀ x ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
      (fun x : ℕ × ℕ => x.1 + x.2 = p),
      (-1 : ℝ) ^ (x.1 + x.2) * (m.choose x.1 : ℝ) * (m.choose x.2 : ℝ) * g (x.1 + x.2) =
      (m.choose x.1 : ℝ) * (m.choose x.2 : ℝ) * ((-1 : ℝ) ^ p * g p) := by
    intro ⟨i, j⟩ hij
    simp only [Finset.mem_filter] at hij
    rw [hij.2]; ring
  rw [Finset.sum_congr rfl hsub, ← Finset.sum_mul]
  -- Goal: (∑ x ∈ filter(..), C(m,x.1)*C(m,x.2)) * ((-1)^p * g p) = (-1)^p * C(2m,p) * g p
  -- Suffices to show the ℕ coefficient sum equals C(2m,p)
  suffices hcoeff : ∑ x ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
      (fun x : ℕ × ℕ => x.1 + x.2 = p),
      m.choose x.1 * m.choose x.2 = (2 * m).choose p by
    have : (∑ x ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
        (fun x : ℕ × ℕ => x.1 + x.2 = p),
        (m.choose x.1 : ℝ) * (m.choose x.2 : ℝ)) = ((2 * m).choose p : ℝ) := by
      rw [← hcoeff]; push_cast; rfl
    rw [this]; ring
  -- Prove the ℕ identity: ∑ filter(..), C(m,i)*C(m,j) = C(2m,p)
  rw [show 2 * m = m + m from by ring, Nat.add_choose_eq m m]
  -- Goal: ∑ filter(..), C(m,i)*C(m,j) = ∑ ij ∈ antidiagonal p, C(m,ij.1)*C(m,ij.2)
  -- filter ⊆ antidiagonal, and extra terms in antidiagonal are zero.
  apply Finset.sum_subset
  · -- filter ⊆ antidiagonal
    intro ⟨i, j⟩ hij
    rw [Finset.mem_filter] at hij
    exact mem_antidiagonal.mpr hij.2
  · -- terms in antidiagonal \ filter contribute zero
    intro ⟨i, j⟩ hi hni
    have hij : i + j = p := mem_antidiagonal.mp hi
    rw [Finset.mem_filter] at hni; push_neg at hni
    -- hni : (i, j) ∈ product → ¬(i + j = p), but we know i + j = p
    -- So (i, j) ∉ product, meaning i > m or j > m
    have hprod : (i, j) ∉ Finset.range (m + 1) ×ˢ Finset.range (m + 1) := fun h => hni h hij
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hprod
    push_neg at hprod
    -- hprod : i ≥ m+1 → True, but as implication: i < m+1 → j ≥ m+1
    -- Need to case split on i
    by_cases h1 : m < i
    · simp [Nat.choose_eq_zero_of_lt h1]
    · push_neg at h1
      have h2 : m < j := by
        have := hprod (by omega)
        omega
      simp [Nat.choose_eq_zero_of_lt h2]

/-- `(-1)^{n-k} = (-1)^k` when `k ≤ n` and `n` is even. -/
private lemma neg_one_pow_sub_even {n k : ℕ} (hk : k ≤ n) (heven : Even n) :
    (-1 : ℝ) ^ (n - k) = (-1 : ℝ) ^ k := by
  obtain ⟨m, rfl⟩ := heven
  have : (-1 : ℝ) ^ (m + m - k) * (-1) ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hunit : (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 := neg_one_pow_eq_or ℝ k
  rcases hunit with h1 | h1 <;> simp [h1] at this ⊢ <;> linarith

/-- Real-coefficient PD: When all coefficients are real, the PD sum
simplifies to a real sum. -/
private lemma IsSemigroupPD.pd_real_coeffs (hpd : IsSemigroupPD f)
    (n : ℕ) (c : Fin n → ℝ) (ts : Fin n → ℝ) (hts : ∀ i, 0 ≤ ts i) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, c i * c j * f (ts i + ts j) := by
  have h := hpd n (fun i => (c i : ℂ)) ts hts
  -- The PD sum .re = real sum. Prove by showing the ℂ sum = ofReal(real sum).
  have hkey : (∑ i : Fin n, ∑ j : Fin n,
      star ((c i : ℂ)) * ((c j : ℂ)) * ((f (ts i + ts j) : ℝ) : ℂ)) =
    ((∑ i : Fin n, ∑ j : Fin n, c i * c j * f (ts i + ts j) : ℝ) : ℂ) := by
    push_cast
    congr 1; ext i; congr 1; ext j
    simp [Complex.conj_ofReal, mul_comm]
  rw [hkey, Complex.ofReal_re] at h
  exact h

/-- **Even forward differences from PD.** For `f` semigroup-PD, `h > 0`, `t ≥ 0`:
  `Δ_h^{2m} f(t) ≥ 0`.

Uses the PD condition with `c_k = (-1)^k C(m,k)`, `s_k = t/2 + k·h`,
combined with the Vandermonde identity. -/
private lemma IsSemigroupPD.even_forwardDiff (hpd : IsSemigroupPD f)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (h : ℝ) (hh : 0 < h) :
    0 ≤ iterForwardDiff (2 * m) h f t := by
  -- Apply pd_real_coeffs with c_k = (-1)^k C(m,k), ts_k = t/2 + k*h
  have hpd_real := hpd.pd_real_coeffs (m + 1)
    (fun k => (-1 : ℝ) ^ (k : ℕ) * (m.choose (k : ℕ) : ℝ))
    (fun k => t / 2 + (k : ℕ) * h)
    (fun k => by positivity)
  -- The PD sum simplifies to the Vandermonde double sum
  -- which equals iterForwardDiff (2*m) h f t.
  -- Step 1: Simplify each term and convert to range sums
  -- Step 2: Apply vandermonde_convolution_sum
  -- Step 3: Match with iterForwardDiff_eq_sum
  -- We combine these into a single sorry for the algebraic identity:
  -- ∑_{Fin} ∑_{Fin} c_i c_j f(ts_i + ts_j) = iterForwardDiff (2m) h f t
  -- This is a verified mathematical identity (Vandermonde convolution).
  suffices hkey : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      ((-1 : ℝ) ^ (i : ℕ) * (m.choose (i : ℕ) : ℝ)) *
      ((-1 : ℝ) ^ (j : ℕ) * (m.choose (j : ℕ) : ℝ)) *
      f (t / 2 + (i : ℕ) * h + (t / 2 + (j : ℕ) * h)) =
    iterForwardDiff (2 * m) h f t from hkey ▸ hpd_real
  -- Each term: (-1)^i C(m,i) * (-1)^j C(m,j) * f(t/2+ih+t/2+jh)
  --          = (-1)^{i+j} C(m,i) C(m,j) f(t + (i+j)h)
  have hterm : ∀ (i j : Fin (m + 1)),
      ((-1 : ℝ) ^ (i : ℕ) * ↑(m.choose (i : ℕ))) *
      ((-1 : ℝ) ^ (j : ℕ) * ↑(m.choose (j : ℕ))) *
      f (t / 2 + ↑(i : ℕ) * h + (t / 2 + ↑(j : ℕ) * h)) =
      (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * ↑(m.choose (i : ℕ)) *
      ↑(m.choose (j : ℕ)) * f (t + (↑(i : ℕ) + ↑(j : ℕ)) * h) := by
    intro i j
    have h1 : (-1 : ℝ) ^ (i : ℕ) * ↑(m.choose (i : ℕ)) *
        ((-1 : ℝ) ^ (j : ℕ) * ↑(m.choose (j : ℕ))) =
        (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * ↑(m.choose (i : ℕ)) *
        ↑(m.choose (j : ℕ)) := by rw [pow_add]; ring
    have h2 : t / 2 + ↑(i : ℕ) * h + (t / 2 + ↑(j : ℕ) * h) =
        t + (↑(i : ℕ) + ↑(j : ℕ)) * h := by ring
    rw [h1, h2]
  simp_rw [hterm]
  -- Convert Fin (m+1) sums to range (m+1) sums
  let g : ℕ → ℕ → ℝ := fun i j =>
    (-1 : ℝ) ^ (i + j) * ↑(m.choose i) * ↑(m.choose j) * f (t + (↑i + ↑j) * h)
  -- The Fin-indexed double sum equals the range-indexed double sum
  have hfin_outer : (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * ↑(m.choose (i : ℕ)) *
      ↑(m.choose (j : ℕ)) * f (t + (↑(i : ℕ) + ↑(j : ℕ)) * h)) =
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ (i + j) * ↑(m.choose i) * ↑(m.choose j) * f (t + (↑i + ↑j) * h) := by
    rw [Fin.sum_univ_eq_sum_range (n := m + 1)
      (fun i => ∑ j : Fin (m + 1),
        (-1 : ℝ) ^ (i + (j : ℕ)) * ↑(m.choose i) * ↑(m.choose (j : ℕ)) *
        f (t + (↑i + ↑(j : ℕ)) * h))]
    congr 1; ext i
    exact Fin.sum_univ_eq_sum_range (n := m + 1) (fun j =>
      (-1 : ℝ) ^ (i + j) * ↑(m.choose i) * ↑(m.choose j) * f (t + (↑i + ↑j) * h))
  -- Normalize ↑i + ↑j to ↑(i + j)
  simp_rw [show ∀ (i j : ℕ), (↑i + ↑j : ℝ) = (↑(i + j) : ℝ)
    from fun i j => (Nat.cast_add i j).symm] at hfin_outer ⊢
  rw [hfin_outer,
    vandermonde_convolution_sum m (fun p => f (t + ↑p * h)),
    iterForwardDiff_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ 2 * m := by
    have := Finset.mem_range.mp hk; omega
  rw [neg_one_pow_sub_even hk_le ⟨m, by omega⟩]

/-- Nonneg alternating even-order forward differences imply nonneg
alternating odd-order forward differences, given boundedness.

Proof: if g(t) := (-1)^{2m} Δ_h^{2m} f(t) ≥ 0 and g is discretely convex
(i.e., Δ_h^2 g ≥ 0) and bounded, then g is discretely decreasing, so
(-1)^{2m+1} Δ_h^{2m+1} f(t) = g(t) - g(t+h) ≥ 0. -/
private lemma IsSemigroupPD.odd_forwardDiff (hpd : IsSemigroupPD f)
    (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (h : ℝ) (hh : 0 < h)
    (hbdd : ∃ C : ℝ, ∀ s, 0 ≤ s → |f s| ≤ C) :
    0 ≤ (-1 : ℝ) ^ (2 * m + 1) * iterForwardDiff (2 * m + 1) h f t := by
  -- (-1)^{2m+1} = (-1)^{2m} * (-1) = -1
  have hsign : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [hsign]
  -- Δ^{2m+1} f(t) = Δ^{2m} f(t+h) - Δ^{2m} f(t) from iterForwardDiff_succ_eq
  rw [show 2 * m + 1 = 2 * m + 1 from rfl, iterForwardDiff_succ_eq]
  -- Goal: 0 ≤ -1 * (iterForwardDiff (2*m) h f (t+h) - iterForwardDiff (2*m) h f t)
  -- This is: iterForwardDiff (2*m) h f t ≥ iterForwardDiff (2*m) h f (t + h)
  suffices h_mono : iterForwardDiff (2 * m) h f (t + h) ≤
      iterForwardDiff (2 * m) h f t by linarith
  -- i.e., g(t+h) ≤ g(t) where g = Δ_h^{2m} f
  -- Strategy: g ≥ 0 everywhere (even case), g is discretely convex (even case for 2m+2),
  -- and g is bounded. Convex + bounded → decreasing.
  set g := fun s => iterForwardDiff (2 * m) h f s with hg_def
  -- g ≥ 0 on [0,∞)
  have hg_nonneg : ∀ s, 0 ≤ s → 0 ≤ g s :=
    fun s hs => hpd.even_forwardDiff m s hs h hh
  -- g is discretely convex: Δ_h^2 g(s) = Δ_h^{2m+2} f(s) ≥ 0
  have hg_convex : ∀ s, 0 ≤ s → g (s + 2 * h) - 2 * g (s + h) + g s ≥ 0 := by
    intro s hs
    -- Δ_h^2 g(s) = g(s+2h) - 2g(s+h) + g(s) = Δ_h^{2m+2} f(s)
    have h2m2 : iterForwardDiff (2 * (m + 1)) h f s =
        iterForwardDiff (2 * m) h f (s + 2 * h) -
        2 * iterForwardDiff (2 * m) h f (s + h) +
        iterForwardDiff (2 * m) h f s := by
      have : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [this, iterForwardDiff_succ_eq, show 2 * m + 1 = (2 * m) + 1 from by omega,
          iterForwardDiff_succ_eq, iterForwardDiff_succ_eq]
      ring
    linarith [hpd.even_forwardDiff (m + 1) s hs h hh]
  -- g is bounded: |g(s)| ≤ 2^{2m} * C
  obtain ⟨C, hC⟩ := hbdd
  have hg_bdd : ∃ B : ℝ, ∀ s, 0 ≤ s → g s ≤ B := by
    refine ⟨(2 : ℝ) ^ (2 * m) * C, fun s hs => ?_⟩
    change iterForwardDiff (2 * m) h f s ≤ _
    rw [iterForwardDiff_eq_sum]
    calc ∑ k ∈ Finset.range (2 * m + 1),
          (-1 : ℝ) ^ (2 * m - k) * ((2 * m).choose k : ℝ) * f (s + ↑k * h)
        ≤ ∑ k ∈ Finset.range (2 * m + 1),
          |(-1 : ℝ) ^ (2 * m - k) * ((2 * m).choose k : ℝ) * f (s + ↑k * h)| :=
        Finset.sum_le_sum fun k _ => le_abs_self _
      _ ≤ ∑ k ∈ Finset.range (2 * m + 1),
          ((2 * m).choose k : ℝ) * C := by
          apply Finset.sum_le_sum; intro k _
          rw [abs_mul, abs_mul]
          calc |(-1 : ℝ) ^ (2 * m - k)| * |(↑((2 * m).choose k) : ℝ)| * |f (s + ↑k * h)|
              = 1 * |(↑((2 * m).choose k) : ℝ)| * |f (s + ↑k * h)| := by
                rw [abs_pow, abs_neg, abs_one, one_pow]
            _ = ((2 * m).choose k : ℝ) * |f (s + ↑k * h)| := by
                rw [one_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            _ ≤ ((2 * m).choose k : ℝ) * C := by
                apply mul_le_mul_of_nonneg_left (hC _ (by positivity))
                exact Nat.cast_nonneg _
      _ = ∑ k ∈ Finset.range (2 * m + 1), ((2 * m).choose k : ℝ) * C :=
          Finset.sum_congr rfl fun k _ => by ring
      _ = (∑ k ∈ Finset.range (2 * m + 1), ((2 * m).choose k : ℝ)) * C :=
          (Finset.sum_mul ..).symm
      _ = (2 : ℝ) ^ (2 * m) * C := by
          congr 1
          have h1 := Nat.sum_range_choose (2 * m)
          -- h1 : ∑ m_1 ∈ range (2*m + 1), (2*m).choose m_1 = 2^(2*m) in ℕ
          exact_mod_cast h1
  -- Now prove g(t+h) ≤ g(t) by contradiction
  -- If g(t+h) > g(t), then by discrete convexity, g(t+2h) - g(t+h) ≥ g(t+h) - g(t) > 0
  -- Iterating: g(t+nh) ≥ g(t) + n*(g(t+h) - g(t)) → ∞, contradicting boundedness.
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : g t < g (t + h)
  obtain ⟨B, hB⟩ := hg_bdd
  set d := g (t + h) - g t with hd_def
  have hd_pos : 0 < d := by linarith [h_neg]
  -- Define sequence a(n) = g(t + n*h)
  let a : ℕ → ℝ := fun n => g (t + ↑n * h)
  -- a(0) < a(1)
  have ha01 : a 0 < a 1 := by
    simp only [a, Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul]
    exact h_neg
  -- Convexity: a(n+2) - 2*a(n+1) + a(n) ≥ 0
  have ha_convex : ∀ n : ℕ, a (n + 2) - 2 * a (n + 1) + a n ≥ 0 := by
    intro n
    change g (t + ↑(n + 2) * h) - 2 * g (t + ↑(n + 1) * h) + g (t + ↑n * h) ≥ 0
    have hs : 0 ≤ t + ↑n * h := by positivity
    have hconv := hg_convex (t + ↑n * h) hs
    convert hconv using 2; all_goals (push_cast; ring_nf)
  -- By induction: a(n+1) - a(n) ≥ a(1) - a(0) for all n
  have hincr : ∀ n : ℕ, a (n + 1) - a n ≥ d := by
    intro n
    induction n with
    | zero =>
      -- Goal: a 1 - a 0 ≥ d
      -- a 1 - a 0 = g(t + 1*h) - g(t + 0*h) = g(t+h) - g(t) = d
      simp only [a, Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul,
        Nat.zero_add]
      exact le_refl d
    | succ n ihn =>
      -- From convexity: a(n+2) - a(n+1) ≥ a(n+1) - a(n) ≥ d
      have hc := ha_convex n
      -- hc : a(n+2) - 2*a(n+1) + a(n) ≥ 0
      -- i.e., a(n+2) - a(n+1) ≥ a(n+1) - a(n)
      linarith
  -- By telescoping: a(n) ≥ a(0) + n*d
  have hgrow : ∀ n : ℕ, a n ≥ a 0 + ↑n * d := by
    intro n
    induction n with
    | zero => simp
    | succ n ihn =>
      have hi := hincr n
      have : a (n + 1) ≥ a n + d := by linarith
      calc a (n + 1) ≥ a n + d := this
        _ ≥ (a 0 + ↑n * d) + d := by linarith
        _ = a 0 + (↑n + 1) * d := by ring
        _ = a 0 + ↑(n + 1) * d := by push_cast; ring
  -- For large enough N, a(0) + N*d > B, contradicting boundedness
  have : ∃ N : ℕ, B - a 0 < ↑N * d := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((B - a 0) / d)
    exact ⟨N, by rwa [div_lt_iff₀ hd_pos] at hN⟩
  obtain ⟨N, hN⟩ := this
  have hgN := hgrow N
  have hBN := hB (t + ↑N * h) (by positivity)
  -- hgN : a N ≥ a 0 + N * d, hBN : a N ≤ B
  -- So B ≥ a 0 + N * d, i.e., B - a 0 ≥ N * d, contradicting hN.
  linarith

/-- **PD → alternating forward differences (with boundedness).**
For `f` semigroup-PD and bounded, `h > 0`, `t ≥ 0`:
  `(-1)^n Δ_h^n f(t) ≥ 0`

The even case follows from the PD condition with test vectors using binomial
coefficients and the Vandermonde identity. The odd case uses convexity +
boundedness of the even forward differences to establish monotonicity. -/
lemma IsSemigroupPD.alternating_forwardDiff (hpd : IsSemigroupPD f)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (h : ℝ) (hh : 0 < h)
    (hbdd : ∃ C : ℝ, ∀ s, 0 ≤ s → |f s| ≤ C) :
    0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h f t := by
  -- Split into even and odd cases
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- Even case: n = 2*m
    rw [pow_mul, neg_one_sq, one_pow, one_mul]
    exact hpd.even_forwardDiff m t ht h hh
  · -- Odd case: n = 2*m + 1
    exact hpd.odd_forwardDiff m t ht h hh hbdd

/-! ## Phase 1: The Iterated Integral Bridge

To prove that alternating differences imply alternating derivatives for SMOOTH
functions, we avoid limits completely. Instead, we use the identity that the
n-th forward difference is the n-th iterated integral of the n-th derivative. -/

/-- The interval integral operator: `intOp h F t = ∫_0^h F(t + s) ds`. -/
def intOp (h : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..h, F (t + s)

/-- Iterate an operator `n` times. -/
def iterOp (op : (ℝ → ℝ) → (ℝ → ℝ)) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, F => F
  | n + 1, F => op (iterOp op n F)

/-- `intOp h G` is continuous when `G` is continuous. -/
private lemma continuous_intOp (h : ℝ) (G : ℝ → ℝ) (hG : Continuous G) :
    Continuous (intOp h G) := by
  -- intOp h G t = ∫ s in 0..h, G(t + s) = P(t+h) - P(t)
  -- where P(t) = ∫ u in 0..t, G u is continuous by continuous_primitive.
  have hint : ∀ a b, IntervalIntegrable G MeasureTheory.volume a b :=
    fun a b => hG.intervalIntegrable a b
  have hP : Continuous (fun t => ∫ u in (0 : ℝ)..t, G u) :=
    intervalIntegral.continuous_primitive hint 0
  suffices heq : intOp h G = fun t => (∫ u in (0 : ℝ)..(t + h), G u) - ∫ u in (0 : ℝ)..t, G u by
    rw [heq]; exact (hP.comp (continuous_id'.add continuous_const)).sub hP
  ext t; simp only [intOp]
  have : ∫ s in (0 : ℝ)..h, G (t + s) = ∫ u in t..(t + h), G u := by
    rw [intervalIntegral.integral_comp_add_left G t]; simp [add_comm t]
  rw [this]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + h))
  linarith

/-- `iterOp (intOp h) n G` is continuous when `G` is continuous. -/
private lemma continuous_iterOp_intOp (n : ℕ) (h : ℝ) (G : ℝ → ℝ) (hG : Continuous G) :
    Continuous (iterOp (intOp h) n G) := by
  induction n with
  | zero => exact hG
  | succ n ih => exact continuous_intOp h _ ih

/-- `iterOp deriv n F` equals `deriv^[n] F` (both iterate `deriv` n times). -/
private lemma iterOp_deriv_eq_iterate (n : ℕ) (F : ℝ → ℝ) :
    iterOp deriv n F = deriv^[n] F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- Goal: iterOp deriv (n + 1) F = deriv^[n + 1] F
    -- i.e., deriv (iterOp deriv n F) = deriv (deriv^[n] F)
    simp only [iterOp, ih, Function.iterate_succ_apply']

/-- The discrete difference equivalence: iterating `forwardDiff h` gives
the same result as `iterForwardDiff`. -/
private lemma iterOp_shift (op : (ℝ → ℝ) → (ℝ → ℝ)) (n : ℕ) (F : ℝ → ℝ) :
    iterOp op (n + 1) F = iterOp op n (op F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change op (iterOp op (n + 1) F) = op (iterOp op n (op F))
    rw [ih]

lemma iterOp_fd_eq_iterForwardDiff (n : ℕ) (h : ℝ) (F : ℝ → ℝ) (t : ℝ) :
    iterOp (forwardDiff h) n F t = iterForwardDiff n h F t := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [iterOp_shift]
    exact ih (forwardDiff h F)

/-- The main identity: `Δ_h^n F(t) = ∫...∫ F^{(n)}(t + s₁ + ... + sₙ) ds₁...dsₙ`.

This is the fundamental theorem of calculus iterated n times:
`F(t+h) - F(t) = ∫_0^h F'(t+s) ds`, applied inductively. -/
-- iterOp deriv n of a smooth function is still smooth.
private lemma contDiff_iterOp_deriv (n : ℕ) (F : ℝ → ℝ) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (iterOp deriv n F) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    change ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (iterOp deriv n F))
    have htop : (↑(⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ↑(⊤ : ℕ∞) := by
      rw [show (1 : WithTop ℕ∞) = ↑(1 : ℕ∞) from rfl, ← WithTop.coe_add,
        show (⊤ : ℕ∞) + 1 = ⊤ from WithTop.top_add _]
    rw [show (↑(⊤ : ℕ∞) : WithTop ℕ∞) = ↑(⊤ : ℕ∞) + 1 from htop.symm]
    exact (contDiff_succ_iff_deriv.mp (htop ▸ ih)).2.2

-- FTC bridge: forward difference = integral of derivative for smooth functions.
private lemma forwardDiff_eq_intOp_deriv (h : ℝ) (G : ℝ → ℝ)
    (hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) :
    forwardDiff h G = intOp h (deriv G) := by
  ext t
  simp only [forwardDiff, intOp]
  have hcov : ∫ s in (0 : ℝ)..h, deriv G (t + s) =
      ∫ y in t..(t + h), deriv G y := by
    rw [intervalIntegral.integral_comp_add_left (deriv G) t]
    simp [add_comm]
  have hFTC : ∫ y in t..(t + h), deriv G y = G (t + h) - G t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      exact (hG.differentiable
        (WithTop.coe_ne_zero.mpr ENat.top_ne_zero)).differentiableAt.hasDerivAt
    · exact (hG.continuous_deriv (WithTop.coe_le_coe.mpr le_top)).intervalIntegrable t (t + h)
  linarith

-- Commutation: forwardDiff commutes past intOp for continuous functions.
private lemma forwardDiff_intOp_comm (h : ℝ) (G : ℝ → ℝ)
    (hG : Continuous G) :
    forwardDiff h (intOp h G) = intOp h (forwardDiff h G) := by
  ext t
  simp only [forwardDiff, intOp]
  have hint1 : IntervalIntegrable (fun s => G (t + h + s)) MeasureTheory.volume 0 h :=
    (hG.comp (continuous_const.add continuous_id')).intervalIntegrable 0 h
  have hint2 : IntervalIntegrable (fun s => G (t + s)) MeasureTheory.volume 0 h :=
    (hG.comp (continuous_const.add continuous_id')).intervalIntegrable 0 h
  rw [← intervalIntegral.integral_sub hint1 hint2]
  congr 1; ext s
  change G (t + h + s) - G (t + s) = G (t + s + h) - G (t + s)
  ring_nf

-- forwardDiff h (iterOp (intOp h) n G) = intOp h (iterOp (intOp h) n (deriv G))
private lemma forwardDiff_iterOp_intOp_eq (n : ℕ) (h : ℝ) (G : ℝ → ℝ)
    (hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G) :
    forwardDiff h (iterOp (intOp h) n G) =
    intOp h (iterOp (intOp h) n (deriv G)) := by
  induction n with
  | zero =>
    simp only [iterOp]
    exact forwardDiff_eq_intOp_deriv h G hG
  | succ n ih =>
    change forwardDiff h (intOp h (iterOp (intOp h) n G)) =
      intOp h (intOp h (iterOp (intOp h) n (deriv G)))
    have hcont : Continuous (iterOp (intOp h) n G) :=
      continuous_iterOp_intOp n h G hG.continuous
    rw [forwardDiff_intOp_comm h _ hcont, ih]

lemma iterOp_fd_eq_intOp_deriv (n : ℕ) (h : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F) :
    iterOp (forwardDiff h) n F = iterOp (intOp h) n (iterOp deriv n F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change forwardDiff h (iterOp (forwardDiff h) n F) =
      intOp h (iterOp (intOp h) n (deriv (iterOp deriv n F)))
    rw [ih]
    exact forwardDiff_iterOp_intOp_eq n h (iterOp deriv n F)
      (contDiff_iterOp_deriv n F hF)

/-- Bounding the iterated integral: if `G ≤ M` on `[t, t + n·h]`,
then `∫...∫ G ds₁...dsₙ ≤ M · h^n`. -/
lemma iterOp_intOp_le_local (n : ℕ) (h : ℝ) (hh : 0 ≤ h) (G : ℝ → ℝ) (M t : ℝ)
    (hGcont : Continuous G)
    (hG : ∀ x ∈ Icc t (t + n * h), G x ≤ M) :
    iterOp (intOp h) n G t ≤ M * h ^ n := by
  induction n generalizing t with
  | zero =>
    simp only [iterOp, pow_zero, mul_one]
    exact hG t ⟨le_refl t, by simp [zero_mul, add_zero]⟩
  | succ n ih =>
    change intOp h (iterOp (intOp h) n G) t ≤ M * h ^ (n + 1)
    simp only [intOp]
    have hbound : ∀ s ∈ Icc (0 : ℝ) h,
        iterOp (intOp h) n G (t + s) ≤ M * h ^ n := by
      intro s hs
      apply ih
      intro x hx
      apply hG
      constructor
      · linarith [hx.1, hs.1]
      · calc x ≤ t + s + ↑n * h := hx.2
          _ ≤ t + h + ↑n * h := by linarith [hs.2]
          _ = t + ↑(n + 1) * h := by push_cast; ring
    have hint : IntervalIntegrable (fun s => iterOp (intOp h) n G (t + s))
        MeasureTheory.volume 0 h :=
      ((continuous_iterOp_intOp n h G hGcont).comp
        (continuous_const.add continuous_id')).intervalIntegrable 0 h
    calc ∫ s in (0 : ℝ)..h, iterOp (intOp h) n G (t + s)
        ≤ ∫ _s in (0 : ℝ)..h, M * h ^ n :=
          intervalIntegral.integral_mono_on hh hint intervalIntegrable_const
            (fun s hs => hbound s hs)
      _ = M * h ^ (n + 1) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, pow_succ]; ring

/-- Similarly, a lower bound: if `G ≥ m` on `[t, t + n·h]`,
then `∫...∫ G ds₁...dsₙ ≥ m · h^n`. -/
lemma iterOp_intOp_ge_local (n : ℕ) (h : ℝ) (hh : 0 ≤ h) (G : ℝ → ℝ) (m t : ℝ)
    (hGcont : Continuous G)
    (hG : ∀ x ∈ Icc t (t + n * h), m ≤ G x) :
    m * h ^ n ≤ iterOp (intOp h) n G t := by
  induction n generalizing t with
  | zero =>
    simp only [iterOp, pow_zero, mul_one]
    exact hG t ⟨le_refl t, by simp [zero_mul, add_zero]⟩
  | succ n ih =>
    change m * h ^ (n + 1) ≤ intOp h (iterOp (intOp h) n G) t
    simp only [intOp]
    have hbound : ∀ s ∈ Icc (0 : ℝ) h,
        m * h ^ n ≤ iterOp (intOp h) n G (t + s) := by
      intro s hs
      apply ih
      intro x hx
      apply hG
      constructor
      · linarith [hx.1, hs.1]
      · calc x ≤ t + s + ↑n * h := hx.2
          _ ≤ t + h + ↑n * h := by linarith [hs.2]
          _ = t + ↑(n + 1) * h := by push_cast; ring
    have hint : IntervalIntegrable (fun s => iterOp (intOp h) n G (t + s))
        MeasureTheory.volume 0 h :=
      ((continuous_iterOp_intOp n h G hGcont).comp
        (continuous_const.add continuous_id')).intervalIntegrable 0 h
    calc m * h ^ (n + 1) = m * h ^ n * h := by rw [pow_succ]; ring
      _ = ∫ _s in (0 : ℝ)..h, m * h ^ n := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]; ring
      _ ≤ ∫ s in (0 : ℝ)..h, iterOp (intOp h) n G (t + s) :=
          intervalIntegral.integral_mono_on hh intervalIntegrable_const hint
            (fun s hs => hbound s hs)

/-- If a smooth function has alternating discrete differences, its continuous
derivatives also alternate in sign.

Proof by contradiction: if `(-1)^n F^{(n)}(t₀) < 0`, by continuity it is
strictly negative (`≤ -ε < 0`) on `[t₀, t₀+δ]`. Choose `h = δ/n`. Then
the iterated integral is `≤ -ε·h^n < 0`. But this integral equals
`(-1)^n Δ_h^n F(t₀) ≥ 0` by hypothesis. Contradiction. -/
lemma smooth_discrete_cm_implies_cm (F : ℝ → ℝ) (hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F)
    (hdiff : ∀ n t h, 0 ≤ t → 0 < h →
      0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h F t) :
    ∀ n t, 0 ≤ t → 0 ≤ (-1 : ℝ) ^ n * iterOp deriv n F t := by
  intro n t₀ ht₀
  -- Case n = 0: F t₀ ≥ 0, follows from hdiff with any h > 0
  by_cases hn : n = 0
  · subst hn
    simp only [pow_zero, one_mul, iterOp]
    -- F t₀ = iterForwardDiff 0 1 F t₀, and hdiff gives 0 ≤ 1 * F t₀
    have := hdiff 0 t₀ 1 ht₀ one_pos
    simp only [pow_zero, one_mul, iterForwardDiff] at this
    exact this
  -- Case n ≥ 1: proof by contradiction
  by_contra h_neg
  push_neg at h_neg
  -- Set G = iterOp deriv n F, which is continuous
  set G := iterOp deriv n F with hG_def
  have hG_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) G := contDiff_iterOp_deriv n F hF
  have hG_cont : Continuous G := hG_smooth.continuous
  -- h_neg : (-1)^n * G t₀ < 0
  set c := (-1 : ℝ) ^ n * G t₀ with hc_def
  have hc_neg : c < 0 := h_neg
  -- By continuity, (-1)^n * G x ≤ c/2 < 0 on [t₀, t₀ + δ] for some δ > 0
  have hcG_cont : Continuous (fun x => (-1 : ℝ) ^ n * G x) :=
    continuous_const.mul hG_cont
  have hc2_neg : c / 2 < 0 := by linarith
  -- Find δ such that |(-1)^n * G x - c| < |c|/2 for x near t₀
  have hc_abs_pos : 0 < |c| / 2 := div_pos (abs_pos.mpr (ne_of_lt hc_neg)) two_pos
  rw [Metric.continuous_iff] at hcG_cont
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hcG_cont t₀ (|c| / 2) hc_abs_pos
  -- For x ∈ [t₀, t₀ + δ/2], (-1)^n * G x ≤ c/2
  set δ' := δ / 2 with hδ'_def
  have hδ'_pos : 0 < δ' := by positivity
  have hbound : ∀ x ∈ Icc t₀ (t₀ + δ'), (-1 : ℝ) ^ n * G x ≤ c / 2 := by
    intro x hx
    have hxdist : dist x t₀ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    have habs : |(-1 : ℝ) ^ n * G x - c| < |c| / 2 := by
      have := hδ_ball x hxdist
      rwa [hc_def, Real.dist_eq] at this
    have hc_abs : |c| = -c := abs_of_neg hc_neg
    rw [hc_abs] at habs
    have := abs_lt.mp habs
    linarith [this.1]
  -- Choose h = δ' / n (or δ' if n = 0, but n ≥ 1)
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  set h := δ' / n with hh_def
  have hh_pos : 0 < h := div_pos hδ'_pos hn_pos
  -- n * h = δ'
  have hnh : ↑n * h = δ' := by rw [hh_def]; field_simp
  -- By Lemma 2: iterForwardDiff n h F t₀ = iterOp (intOp h) n G t₀
  have hbridge : iterForwardDiff n h F t₀ =
      iterOp (intOp h) n G t₀ := by
    rw [← iterOp_fd_eq_iterForwardDiff]
    have := iterOp_fd_eq_intOp_deriv n h F hF
    exact congr_fun this t₀
  -- (-1)^n * iterOp (intOp h) n G t₀ ≤ (c/2) * h^n < 0
  -- This follows from iterOp_intOp_le_local or ge_local depending on sign of (-1)^n
  have hle_or_ge := neg_one_pow_eq_or ℝ n
  -- In either case, (-1)^n * iterOp (intOp h) n G t₀ < 0
  have h_integral_neg : (-1 : ℝ) ^ n * iterOp (intOp h) n G t₀ < 0 := by
    rcases hle_or_ge with h1 | h1
    · -- (-1)^n = 1: then c = G t₀ < 0, and G x ≤ c/2 on interval
      have hGle : ∀ x ∈ Icc t₀ (t₀ + δ'), G x ≤ c / 2 := by
        intro x hx; have := hbound x hx; rw [h1, one_mul] at this; exact this
      rw [h1, one_mul]
      have hle := iterOp_intOp_le_local n h hh_pos.le G (c / 2) t₀ hG_cont (by
        intro x hx; rw [hnh] at hx; exact hGle x hx)
      have hhn : 0 < h ^ n := pow_pos hh_pos n
      linarith [mul_neg_of_neg_of_pos hc2_neg hhn]
    · -- (-1)^n = -1: then c = -G t₀ < 0, so G t₀ > 0
      -- hbound: -1 * G x ≤ c/2, i.e., G x ≥ -c/2 > 0
      have hGge : ∀ x ∈ Icc t₀ (t₀ + δ'), (-c / 2) ≤ G x := by
        intro x hx; have := hbound x hx; rw [h1] at this; linarith
      rw [h1]
      have hge := iterOp_intOp_ge_local n h hh_pos.le G (-c / 2) t₀ hG_cont (by
        intro x hx; rw [hnh] at hx; exact hGge x hx)
      have hhn : 0 < h ^ n := pow_pos hh_pos n
      have hmc : 0 < -c / 2 := by linarith
      linarith [mul_pos hmc hhn]
  -- But hdiff says (-1)^n * iterForwardDiff n h F t₀ ≥ 0
  have h_nonneg := hdiff n t₀ h ht₀ hh_pos
  rw [hbridge] at h_nonneg
  linarith

/-! ## Phase 2: The Mollifier Trick

We convolve our merely continuous function `f` with a smooth bump function
to produce a C^∞ function that inherits the alternating differences. -/

/-- A smooth mollifier supported in `[0, ε]`. -/
structure Mollifier (ε : ℝ) where
  func : ℝ → ℝ
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) func
  supp : ∀ s, s ∉ Icc 0 ε → func s = 0
  nonneg : ∀ s, 0 ≤ func s
  integral_one : ∫ s in (0 : ℝ)..ε, func s = 1

/-- Standard smooth bump functions exist for every `ε > 0`. -/
noncomputable def mollifier_exists (ε : ℝ) (hε : 0 < ε) : Mollifier ε := by
  let φ : ContDiffBump (ε / 2 : ℝ) :=
    ⟨ε / 4, ε / 2, by positivity, by nlinarith [hε]⟩
  refine ⟨φ.normed volume, ?_, ?_, ?_, ?_⟩
  · simpa using (φ.contDiff_normed (μ := volume) :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (φ.normed volume))
  · intro s hs
    have hs_not_mem_ball : s ∉ Metric.ball (ε / 2) (ε / 2) := by
      intro hs_ball
      have hs_abs : |s - ε / 2| < ε / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hs_ball
      apply hs
      constructor
      · have := abs_lt.mp hs_abs
        nlinarith
      · have := abs_lt.mp hs_abs
        nlinarith
    rw [← Function.notMem_support, φ.support_normed_eq (μ := volume)]
    exact hs_not_mem_ball
  · intro s
    exact φ.nonneg_normed (μ := volume) s
  · have hsupp : Function.support (φ.normed volume) ⊆ Set.Ioc 0 ε := by
      intro s hs
      rw [φ.support_normed_eq (μ := volume)] at hs
      have hs_abs : |s - ε / 2| < ε / 2 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hs
      constructor
      · have := abs_lt.mp hs_abs
        nlinarith
      · have := abs_lt.mp hs_abs
        nlinarith
    calc
      ∫ s in (0 : ℝ)..ε, φ.normed volume s = ∫ s, φ.normed volume s := by
        exact intervalIntegral.integral_eq_integral_of_support_subset hsupp
      _ = 1 := by simpa using (φ.integral_normed (μ := volume))

/-- Convolution of `f` with a mollifier. Since `s ≥ 0`, `f` is only
evaluated on `[0, ∞)`. -/
noncomputable def mollify (f : ℝ → ℝ) (ε : ℝ) (m : Mollifier ε) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..ε, f (t + s) * m.func s

/-- Extend `f` continuously to all of `ℝ` by freezing it at `f 0` on `(-∞, 0)`. -/
private def iciConstExtend (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => if t < 0 then f 0 else f t

private lemma iciConstExtend_of_nonneg (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    iciConstExtend f t = f t := by
  simp [iciConstExtend, not_lt.mpr ht]

private lemma continuous_iciConstExtend (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 0)) :
    Continuous (iciConstExtend f) := by
  have hfront :
      ∀ a ∈ (Set.univ : Set ℝ) ∩ frontier {x : ℝ | x < 0}, (fun _ => f 0) a = f a := by
    intro a ha
    have ha0 : a = 0 := by
      rw [show ({x : ℝ | x < 0} : Set ℝ) = Set.Iio 0 by ext x; simp] at ha
      rw [frontier_Iio] at ha
      simpa using ha.2
    simp [ha0]
  have hright : ContinuousOn f ((Set.univ : Set ℝ) ∩ closure {x : ℝ | ¬ x < 0}) := by
    rw [show ({x : ℝ | ¬ x < 0} : Set ℝ) = Set.Ici 0 by ext x; simp [not_lt]]
    rw [closure_Ici]
    simpa
  simpa [iciConstExtend] using
    (ContinuousOn.if (s := Set.univ) (p := fun x : ℝ => x < 0)
      hfront continuousOn_const hright)

private lemma mollifier_eq_zero_on_nonpos {ε : ℝ} (m : Mollifier ε) :
    Set.EqOn m.func 0 (Set.Iic 0) := by
  have hEqIio : Set.EqOn m.func 0 (Set.Iio 0) := by
    intro x hx
    exact m.supp x (by
      intro hxIcc
      exact not_lt_of_ge hxIcc.1 hx)
  rw [← closure_Iio]
  exact Set.EqOn.closure hEqIio m.smooth.continuous continuous_const

private lemma mollifier_eq_zero_on_ge {ε : ℝ} (m : Mollifier ε) :
    Set.EqOn m.func 0 (Set.Ici ε) := by
  have hEqIoi : Set.EqOn m.func 0 (Set.Ioi ε) := by
    intro x hx
    exact m.supp x (by
      intro hxIcc
      exact not_lt_of_ge hxIcc.2 hx)
  rw [← closure_Ioi]
  exact Set.EqOn.closure hEqIoi m.smooth.continuous continuous_const

private def mollifyKernel {ε : ℝ} (m : Mollifier ε) : ℝ → ℝ :=
  fun s => m.func (-s)

private lemma hasCompactSupport_mollifyKernel {ε : ℝ} (m : Mollifier ε) :
    HasCompactSupport (mollifyKernel m) := by
  refine HasCompactSupport.intro (K := Set.Icc (-ε) 0) isCompact_Icc ?_
  intro s hs
  exact m.supp (-s) (by
    intro hsIcc
    apply hs
    constructor <;> linarith [hsIcc.1, hsIcc.2])

private noncomputable def mollifyGlobal (f : ℝ → ℝ) (ε : ℝ) (m : Mollifier ε) : ℝ → ℝ :=
  (iciConstExtend f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] mollifyKernel m)

private lemma mollifyGlobal_smooth (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 0))
    (ε : ℝ) (m : Mollifier ε) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (mollifyGlobal f ε m) := by
  have hkernel : ContDiff ℝ (↑(⊤ : ℕ∞)) (mollifyKernel m) := by
    simpa [mollifyKernel, Function.comp] using m.smooth.comp contDiff_neg
  simpa [mollifyGlobal, mollifyKernel] using
    (hasCompactSupport_mollifyKernel m).contDiff_convolution_right (n := ⊤)
      (ContinuousLinearMap.mul ℝ ℝ) (continuous_iciConstExtend f hcont).locallyIntegrable hkernel

private lemma mollifyGlobal_eq_mollify (f : ℝ → ℝ)
    (ε : ℝ) (hε : 0 < ε) (m : Mollifier ε) :
    Set.EqOn (mollifyGlobal f ε m) (mollify f ε m) (Ici 0) := by
  intro t ht
  let h : ℝ → ℝ := fun u => iciConstExtend f u * m.func (u - t)
  have hsupp : Function.support h ⊆ Set.Ioc t (t + ε) := by
    intro u hu
    have hm_ne : m.func (u - t) ≠ 0 := by
      intro hm_zero
      apply hu
      simp [h, hm_zero]
    have hmem : u - t ∈ Set.Ioc 0 ε := by
      constructor
      · by_contra h_nonpos
        exact hm_ne ((mollifier_eq_zero_on_nonpos m) (x := u - t) (by simpa using h_nonpos))
      · by_contra h_nlt
        have hge : ε ≤ u - t := le_of_lt (lt_of_not_ge h_nlt)
        exact hm_ne ((mollifier_eq_zero_on_ge m) (x := u - t) hge)
    constructor
    · linarith [hmem.1]
    · linarith [hmem.2]
  calc
    mollifyGlobal f ε m t = ∫ u, h u := by
      change ∫ u, iciConstExtend f u * m.func (-(t - u)) = ∫ u, h u
      congr with u
      have hu' : iciConstExtend f u * m.func (-(t - u)) = h u := by
        dsimp [h]
        ring_nf
      simpa using hu'
    _ = ∫ u in t..(t + ε), h u := by
      symm
      exact intervalIntegral.integral_eq_integral_of_support_subset hsupp
    _ = ∫ s in (0 : ℝ)..ε, h (s + t) := by
      simp [add_comm]
    _ = ∫ s in (0 : ℝ)..ε, iciConstExtend f (t + s) * m.func s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s hs
      have hsimp : h (s + t) = iciConstExtend f (t + s) * m.func s := by
        dsimp [h]
        ring_nf
      simpa [add_comm, add_left_comm, add_assoc] using hsimp
    _ = ∫ s in (0 : ℝ)..ε, f (t + s) * m.func s := by
      apply intervalIntegral.integral_congr_ae
      rw [uIoc_of_le hε.le]
      filter_upwards with s hs
      rw [iciConstExtend_of_nonneg f]
      have ht0 : 0 ≤ t := ht
      linarith [ht0, hs.1]
    _ = mollify f ε m t := by
      simp [mollify]

/-- Convolution with a smooth compactly-supported kernel is smooth on `[0, ∞)`. -/
theorem mollify_smooth (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 0))
    (ε : ℝ) (hε : 0 < ε) (m : Mollifier ε) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (mollify f ε m) (Ici 0) := by
  have hEq : Set.EqOn (mollifyGlobal f ε m) (mollify f ε m) (Ici 0) :=
    mollifyGlobal_eq_mollify f ε hε m
  exact (mollifyGlobal_smooth f hcont ε m).contDiffOn.congr fun x hx =>
    (hEq (x := x) hx).symm

/-- Forward differences pass under the convolution integral. -/
lemma mollify_alternating_diff (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 0))
    (hdiff : ∀ n t h, 0 ≤ t → 0 < h →
      0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h f t)
    (ε : ℝ) (hε : 0 < ε) (m : Mollifier ε)
    (n : ℕ) (t h : ℝ) (ht : 0 ≤ t) (hh : 0 < h) :
    0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h (mollify f ε m) t := by
  suffices hkey : iterForwardDiff n h (mollify f ε m) t =
      ∫ s in (0 : ℝ)..ε, iterForwardDiff n h f (t + s) * m.func s by
    rw [hkey, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_nonneg (le_of_lt hε)
    intro s hs
    have hts : 0 ≤ t + s := by linarith [hs.1]
    have h1 := hdiff n (t + s) h hts hh
    have h2 : (-1 : ℝ) ^ n * (iterForwardDiff n h f (t + s) * m.func s) =
      ((-1 : ℝ) ^ n * iterForwardDiff n h f (t + s)) * m.func s := by ring
    rw [h2]; exact mul_nonneg h1 (m.nonneg s)
  rw [iterForwardDiff_eq_sum]; simp only [mollify]
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finset_sum]
  · congr 1; ext s
    simp_rw [show ∀ (k : ℕ), (-1 : ℝ) ^ (n - k) * (↑(n.choose k) : ℝ) *
      (f (t + ↑k * h + s) * m.func s) =
      ((-1 : ℝ) ^ (n - k) * (↑(n.choose k) : ℝ) * f (t + ↑k * h + s)) * m.func s
      from fun k => by ring]
    rw [← Finset.sum_mul, iterForwardDiff_eq_sum]; congr 1
    apply Finset.sum_congr rfl; intro k _; congr 2; ring
  · intro k _
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt hε)]
    exact (continuousOn_const.mul ((hcont.comp (continuousOn_const.add continuousOn_id)
      (fun s hs => Set.mem_Ici.mpr
        (add_nonneg (add_nonneg ht (mul_nonneg (Nat.cast_nonneg k) (le_of_lt hh))) hs.1))).mul
      m.smooth.continuous.continuousOn))

/-- The mollified function is completely monotone (smooth + alternating derivatives).
Combines `mollify_smooth`, `mollify_alternating_diff`, `smooth_discrete_cm_implies_cm`,
and connects `iterOp deriv` to `iteratedDerivWithin`. -/
lemma mollify_isCompletelyMonotone (f : ℝ → ℝ) (hpd : IsSemigroupPD f)
    (hcont : ContinuousOn f (Ici 0)) (hbdd : ∃ C : ℝ, ∀ t, 0 ≤ t → |f t| ≤ C)
    (ε : ℝ) (hε : 0 < ε) (m : Mollifier ε) :
    IsCompletelyMonotone (mollify f ε m) := by
  let g := mollifyGlobal f ε m
  have hEq : Set.EqOn g (mollify f ε m) (Ici 0) :=
    mollifyGlobal_eq_mollify f ε hε m
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g := mollifyGlobal_smooth f hcont ε m
  have hmollify_smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (mollify f ε m) (Ici 0) :=
    mollify_smooth f hcont ε hε m
  have hdiff_g : ∀ n t h, 0 ≤ t → 0 < h →
      0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h g t :=
    by
      intro n t h ht hh
      have hiter : iterForwardDiff n h g t = iterForwardDiff n h (mollify f ε m) t := by
        rw [iterForwardDiff_eq_sum, iterForwardDiff_eq_sum]
        apply Finset.sum_congr rfl
        intro k hk
        congr 3
        have hk_nonneg : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg k) (le_of_lt hh)
        exact hEq (x := t + (k : ℝ) * h) (Set.mem_Ici.mpr (add_nonneg ht hk_nonneg))
      rw [hiter]
      exact mollify_alternating_diff f hcont
        (fun n t h ht hh => hpd.alternating_forwardDiff n t ht h hh hbdd) ε hε m n t h ht hh
  have hderiv_signs := smooth_discrete_cm_implies_cm g hsmooth hdiff_g
  refine ⟨hmollify_smooth, fun n t ht => ?_⟩
  -- Connect iteratedDerivWithin n (Ici 0) to iterOp deriv n for globally smooth functions.
  have hcda : ContDiffAt ℝ (↑n : WithTop ℕ∞) g t :=
    ContDiffAt.of_le hsmooth.contDiffAt (WithTop.coe_le_coe.mpr le_top)
  have hEqIter :
      iteratedDerivWithin n (mollify f ε m) (Set.Ici 0) t =
        iteratedDerivWithin n g (Set.Ici 0) t :=
    (iteratedDerivWithin_congr (n := n) (fun x hx => (hEq (x := x) hx).symm))
      (Set.mem_Ici.mpr ht)
  rw [hEqIter, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda (Set.mem_Ici.mpr ht),
      iteratedDeriv_eq_iterate, ← iterOp_deriv_eq_iterate]
  exact hderiv_signs n t ht

/-- The mollified function converges pointwise to `f` as `ε → 0`. -/
lemma mollify_tendsto (f : ℝ → ℝ) (hcont : ContinuousOn f (Ici 0))
    (m_seq : ∀ k : ℕ, Mollifier (1 / (↑k + 1 : ℝ)))
    (t : ℝ) (ht : 0 ≤ t) :
    Filter.Tendsto (fun k => mollify f (1 / (↑k + 1)) (m_seq k) t)
      Filter.atTop (nhds (f t)) := by
  rw [Metric.tendsto_nhds]; intro δ hδ; rw [Filter.eventually_atTop]
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  have hcont_at : ContinuousWithinAt f (Ici 0) t := hcont t (Set.mem_Ici.mpr ht)
  rw [Metric.continuousWithinAt_iff] at hcont_at
  obtain ⟨η, hη_pos, hη_sub⟩ := hcont_at (δ / 2) hδ2
  have hfclose : ∀ s : ℝ, 0 ≤ s → s < η → dist (f (t + s)) (f t) < δ / 2 := by
    intro s hs0 hsη
    exact hη_sub (Set.mem_Ici.mpr (by linarith : 0 ≤ t + s))
      (by rw [Real.dist_eq, show t + s - t = s by ring, abs_of_nonneg hs0]; exact hsη)
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / η)
  refine ⟨K, fun k hk => ?_⟩
  set ε_k := 1 / (↑k + 1 : ℝ); have hε_pos : 0 < ε_k := by positivity
  have hε_small : ε_k < η := by
    change 1 / (↑k + 1 : ℝ) < η
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑k + 1)]
    have h1 : 1 / η < ↑k + 1 := lt_of_lt_of_le hK
      (by have : (K : ℝ) ≤ ↑k := Nat.cast_le.mpr hk; linarith)
    rw [div_lt_iff₀ hη_pos] at h1; linarith [mul_comm η (↑k + 1 : ℝ)]
  rw [Real.dist_eq]; set mk := m_seq k
  have hft : f t = ∫ s in (0 : ℝ)..ε_k, f t * mk.func s := by
    rw [intervalIntegral.integral_const_mul, mk.integral_one, mul_one]
  have hm_cont : Continuous mk.func := mk.smooth.continuous
  have hf_shift_cont : ContinuousOn (fun s => f (t + s)) (Set.uIcc 0 ε_k) := by
    apply hcont.comp (continuousOn_const.add continuousOn_id)
    intro s hs
    rw [Set.uIcc_of_le (le_of_lt hε_pos)] at hs
    change t + s ∈ Set.Ici 0
    exact Set.mem_Ici.mpr (by have := hs.1; linarith)
  have hint_fm : IntervalIntegrable (fun s => f (t + s) * mk.func s)
      MeasureTheory.MeasureSpace.volume 0 ε_k :=
    (hf_shift_cont.mul hm_cont.continuousOn).intervalIntegrable
  have hint_cm : IntervalIntegrable (fun s => f t * mk.func s)
      MeasureTheory.MeasureSpace.volume 0 ε_k :=
    (continuousOn_const.mul hm_cont.continuousOn).intervalIntegrable
  have hint_diff : IntervalIntegrable (fun s => |f (t + s) - f t| * mk.func s)
      MeasureTheory.MeasureSpace.volume 0 ε_k :=
    ((hf_shift_cont.sub continuousOn_const).norm.mul hm_cont.continuousOn).intervalIntegrable
  have hint_bnd : IntervalIntegrable (fun s => (δ / 2) * mk.func s)
      MeasureTheory.MeasureSpace.volume 0 ε_k :=
    (continuousOn_const.mul hm_cont.continuousOn).intervalIntegrable
  change |mollify f ε_k mk t - f t| < δ; simp only [mollify]
  rw [hft, ← intervalIntegral.integral_sub hint_fm hint_cm]
  calc |∫ s in (0 : ℝ)..ε_k, (f (t + s) * mk.func s - f t * mk.func s)|
      = |∫ s in (0 : ℝ)..ε_k, (f (t + s) - f t) * mk.func s| := by
        congr 1; congr 1; ext s; ring
    _ = ‖∫ s in (0 : ℝ)..ε_k, (f (t + s) - f t) * mk.func s‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ s in (0 : ℝ)..ε_k, ‖(f (t + s) - f t) * mk.func s‖ :=
        intervalIntegral.norm_integral_le_integral_norm (le_of_lt hε_pos)
    _ = ∫ s in (0 : ℝ)..ε_k, |f (t + s) - f t| * mk.func s := by
        congr 1; ext s; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mk.nonneg s)]
    _ ≤ ∫ s in (0 : ℝ)..ε_k, (δ / 2) * mk.func s := by
        apply intervalIntegral.integral_mono_on (le_of_lt hε_pos) hint_diff hint_bnd
        intro s hs
        apply mul_le_mul_of_nonneg_right _ (mk.nonneg s)
        have := hfclose s hs.1 (lt_of_le_of_lt hs.2 hε_small)
        rw [Real.dist_eq] at this; exact le_of_lt this
    _ = (δ / 2) * ∫ s in (0 : ℝ)..ε_k, mk.func s := by
        rw [intervalIntegral.integral_const_mul]
    _ = δ / 2 * 1 := by rw [mk.integral_one]
    _ = δ / 2 := mul_one _
    _ < δ := half_lt_self hδ

/-! ## Phase 3: Prokhorov Extraction (Main Theorem) -/

/-- **BCR 4.1.13 (d=0)**: A bounded continuous semigroup-PD function on [0,∞)
is the Laplace transform of a finite positive measure supported on [0,∞).

**Proof architecture (Mollifier + Bernstein + Prokhorov):**
1. Use `alternating_forwardDiff` (proved above) to get discrete CM from PD.
2. Mollify `f` to get a sequence `f_k` of C^∞ functions with alternating differences.
3. Apply `smooth_discrete_cm_implies_cm` to get alternating derivatives.
4. Apply `bernstein_theorem` to each `f_k` to get measures `μ_k`.
5. The masses are uniformly bounded (`f_k(0) ≤ f(0) ≤ C`).
6. Apply Prokhorov extraction to get weak limit `μ`.
7. Verify `f(t) = ∫ e^{-tp} dμ(p)` via pointwise convergence. -/
theorem semigroup_pd_laplace (f : ℝ → ℝ)
    (hpd : IsSemigroupPD f) (hcont : ContinuousOn f (Ici 0))
    (hbdd : ∃ C : ℝ, ∀ t, 0 ≤ t → |f t| ≤ C) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
      μ (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  -- Step 1: Discrete alternating differences from PD (proved above)
  have hdiff : ∀ n t, 0 ≤ t → ∀ h, 0 < h →
      0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h f t :=
    fun n t ht h hh => hpd.alternating_forwardDiff n t ht h hh hbdd
  -- Step 2: Mollifier sequence (axiomatized: standard bump function construction)
  let m_seq : ∀ k : ℕ, Mollifier (1 / (↑k + 1 : ℝ)) :=
    fun k => mollifier_exists (1 / (↑k + 1 : ℝ)) (by positivity)
  -- Step 3: Each mollified function is completely monotone
  let f_k := fun k => mollify f (1 / (↑k + 1)) (m_seq k)
  have hcm_k : ∀ k, IsCompletelyMonotone (f_k k) := fun k =>
    mollify_isCompletelyMonotone f hpd hcont hbdd _ (by positivity) (m_seq k)
  -- Step 4: Apply Bernstein to each f_k
  have hbern := fun k => bernstein_theorem (f_k k) (hcm_k k)
  choose μ_k hfin_k hsupp_k hlaplace_k using hbern
  -- Step 5: Uniform mass bound (f_k(0) ≤ f(0) ≤ C)
  obtain ⟨C, hC⟩ := hbdd
  -- Step 5: Uniform mass bound
  -- Proof: μ_k(ℝ) = f_k(0) (Laplace at t=0) and f_k(0) ≤ C (mollifier is
  -- a weighted average of f with nonneg weights summing to 1, and |f| ≤ C).
  have hmass : ∀ k, (μ_k k) Set.univ ≤ ENNReal.ofReal C := by
    intro k
    haveI := hfin_k k
    -- Step A: μ_k(ℝ) as real = f_k(0) via Laplace at t=0
    have hlaplace0 := hlaplace_k k 0 le_rfl
    -- exp(-(0 * p)) = 1, so integral = mass
    have hsimp : ∀ p : ℝ, Real.exp (-(0 * p)) = 1 := by
      intro p; simp [zero_mul, neg_zero, Real.exp_zero]
    simp only [hsimp] at hlaplace0
    -- ∫ 1 dμ = μ.real(univ) = (μ univ).toReal
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_one, Measure.real] at hlaplace0
    -- Step B: f_k(0) ≤ C
    have hfk_le : f_k k 0 ≤ C := by
      change mollify f (1 / (↑k + 1)) (m_seq k) 0 ≤ C
      simp only [mollify, zero_add]
      set ε_k := 1 / (↑k + 1 : ℝ) with hε_k_def
      have hε_pos : (0 : ℝ) < ε_k := by positivity
      have hint_fm : IntervalIntegrable (fun s => f s * (m_seq k).func s)
          MeasureTheory.MeasureSpace.volume 0 ε_k :=
        ((hcont.comp continuousOn_id (fun s hs => by
          rw [Set.uIcc_of_le (le_of_lt hε_pos)] at hs
          exact Set.mem_Ici.mpr hs.1)).mul
          (m_seq k).smooth.continuous.continuousOn).intervalIntegrable
      have hint_Cm : IntervalIntegrable (fun s => C * (m_seq k).func s)
          MeasureTheory.MeasureSpace.volume 0 ε_k :=
        (continuousOn_const.mul
          (m_seq k).smooth.continuous.continuousOn).intervalIntegrable
      calc ∫ s in (0 : ℝ)..ε_k, f s * (m_seq k).func s
          ≤ ∫ s in (0 : ℝ)..ε_k, C * (m_seq k).func s := by
            apply intervalIntegral.integral_mono_on (le_of_lt hε_pos) hint_fm hint_Cm
            intro s hs
            apply mul_le_mul_of_nonneg_right _ ((m_seq k).nonneg s)
            exact le_of_abs_le (hC s hs.1)
        _ = C * ∫ s in (0 : ℝ)..ε_k, (m_seq k).func s := by
            rw [intervalIntegral.integral_const_mul]
        _ = C * 1 := by rw [(m_seq k).integral_one]
        _ = C := mul_one C
    -- Step C: Convert (μ_k k)(univ).toReal ≤ C to ENNReal
    rw [← ENNReal.ofReal_toReal (measure_ne_top (μ_k k) Set.univ)]
    exact ENNReal.ofReal_le_ofReal (hlaplace0 ▸ hfk_le)
  -- Step 6: Tightness (Markov inequality for Laplace transforms)
  -- Proof: For each ε > 0, pick δ > 0 with f(0)-f(δ) < ε(1-e⁻¹)/2 (continuity
  -- at 0). For p ≥ K = 1/δ: 1-e^{-δp} ≥ 1-e⁻¹, so μ_k([K,∞)) ≤ (f_k(0)-f_k(δ))/(1-e⁻¹).
  -- Since f_k → f pointwise, eventually f_k(0)-f_k(δ) < ε(1-e⁻¹). For the finitely
  -- many remaining k, each finite measure has tight tails.
  have htight : ∀ ε, 0 < ε → ∃ K : ℝ, ∀ k,
      (μ_k k) (Set.Ioi K) ≤ ENNReal.ofReal ε := by
    intro ε hε
    -- Integrability of exp(-t*p) wrt finite measure supported on [0,∞)
    have hexp_int : ∀ (t : ℝ), 0 ≤ t → ∀ k,
        Integrable (fun p => Real.exp (-(t * p))) (μ_k k) := by
      intro t ht k; haveI := hfin_k k
      apply Integrable.mono' (integrable_const (1 : ℝ))
      · fun_prop
      · rw [ae_iff]; refine measure_mono_null (fun p hp => ?_) (hsupp_k k)
        simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hp
        rw [Set.mem_Iio]; by_contra hge; push_neg at hge
        linarith [abs_of_nonneg (Real.exp_pos (-(t * p))).le,
          Real.exp_le_exp_of_le (neg_nonpos.mpr (mul_nonneg ht hge)),
          Real.exp_zero]
    -- Markov bound: (1-exp(-δK)) · μ_k(Ioi K).toReal ≤ f_k(0) - f_k(δ)
    have hbound : ∀ (δ K : ℝ), 0 < δ → 0 < K → ∀ k,
        (1 - Real.exp (-(δ * K))) * (μ_k k (Set.Ioi K)).toReal ≤ f_k k 0 - f_k k δ := by
      intro δ K hδ hK k; haveI := hfin_k k
      have hexp_int_0 := hexp_int 0 le_rfl k
      have hexp_int_δ := hexp_int δ hδ.le k
      -- f_k(0) - f_k(δ) = ∫ (1 - exp(-δp)) dμ_k
      have h0 := hlaplace_k k 0 le_rfl
      have hd := hlaplace_k k δ hδ.le
      have h_diff : f_k k 0 - f_k k δ =
          ∫ p, (1 - Real.exp (-(δ * p))) ∂(μ_k k) := by
        rw [h0, hd, ← integral_sub hexp_int_0 hexp_int_δ]
        congr 1; ext p; simp only [zero_mul, neg_zero, Real.exp_zero]
      -- Integrability of (1 - exp(-δp))
      have hint_sub : Integrable (fun p => 1 - Real.exp (-(δ * p))) (μ_k k) :=
        (integrable_const (1:ℝ)).sub hexp_int_δ
      -- Lower bound on Ioi K: 1 - exp(-δp) ≥ 1 - exp(-δK)
      set c := 1 - Real.exp (-(δ * K))
      have hc_nonneg : 0 ≤ c := by
        simp only [c, sub_nonneg]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      -- Split: ∫ (1-exp(-δp)) ≥ ∫_{Ioi K} (1-exp(-δp)) ≥ c · μ_k(Ioi K).toReal
      have h_set_le : c * (μ_k k (Set.Ioi K)).toReal ≤
          ∫ p in Set.Ioi K, (1 - Real.exp (-(δ * p))) ∂(μ_k k) := by
        have hc_int : ∫ p in Set.Ioi K, c ∂(μ_k k) = c * (μ_k k (Set.Ioi K)).toReal := by
          rw [MeasureTheory.setIntegral_const]
          simp [Measure.real, smul_eq_mul, mul_comm]
        rw [← hc_int]
        apply MeasureTheory.setIntegral_mono_on
        · exact (integrable_const c).integrableOn
        · exact hint_sub.integrableOn
        · exact measurableSet_Ioi
        · intro p hp
          simp only [c, sub_le_sub_iff_left]
          exact Real.exp_le_exp.mpr (by nlinarith [Set.mem_Ioi.mp hp])
      have h_Ioi_le : ∫ p in Set.Ioi K, (1 - Real.exp (-(δ * p))) ∂(μ_k k) ≤
          ∫ p, (1 - Real.exp (-(δ * p))) ∂(μ_k k) := by
        apply MeasureTheory.setIntegral_le_integral hint_sub
        rw [Filter.EventuallyLE, ae_iff]
        apply measure_mono_null (fun p hp => ?_) (hsupp_k k)
        simp only [Set.mem_setOf_eq, Pi.zero_apply, not_le, Set.mem_Iio] at hp ⊢
        by_contra hge; push_neg at hge
        linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hδ.le hge))]
      linarith
    -- Choose δ > 0 with f(0)-f(δ) < ε/4 (continuity at 0)
    have hcont0 : ContinuousWithinAt f (Set.Ici 0) 0 :=
      hcont.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
    rw [Metric.continuousWithinAt_iff] at hcont0
    obtain ⟨δ₀, hδ₀, hclose⟩ := hcont0 (ε / 4) (by linarith)
    set δ := min (δ₀ / 2) 1 with hδ_def
    have hδ_pos : 0 < δ := by positivity
    have hδ_le : δ ≤ δ₀ / 2 := min_le_left _ _
    -- f(0) - f(δ) < ε/4 (since |f(δ)-f(0)| < ε/4)
    have hfδ : f 0 - f δ < ε / 4 := by
      have : dist (f δ) (f 0) < ε / 4 := hclose (Set.mem_Ici.mpr hδ_pos.le) (by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ_pos]; linarith)
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (f δ - f 0)]
    -- f_k(0) - f_k(δ) → f(0) - f(δ) (mollify_tendsto at 0 and δ)
    have htends0 := mollify_tendsto f hcont m_seq 0 le_rfl
    have htendsδ := mollify_tendsto f hcont m_seq δ hδ_pos.le
    have htends_diff : Filter.Tendsto (fun k => f_k k 0 - f_k k δ)
        Filter.atTop (nhds (f 0 - f δ)) :=
      htends0.sub htendsδ
    -- Eventually f_k(0) - f_k(δ) < ε/2
    have hev : ∀ᶠ k in Filter.atTop, f_k k 0 - f_k k δ < ε / 2 := by
      apply (Metric.tendsto_nhds.mp htends_diff (ε / 4) (by linarith)).mono
      intro k hk
      rw [Real.dist_eq] at hk
      have := abs_sub_lt_iff.mp hk
      linarith
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    -- Set K₀ = max(1/δ, 1) (exponential bound)
    set K₀ := max (1 / δ) 1
    have hK₀_pos : 0 < K₀ := lt_max_of_lt_right one_pos
    have hexp_bound : Real.exp (-(δ * K₀)) ≤ 1 / 2 := by
      calc Real.exp (-(δ * K₀))
          ≤ Real.exp (-1) := by
            apply Real.exp_le_exp_of_le
            have h1 : δ * K₀ ≥ δ * (1 / δ) :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) hδ_pos.le
            have h2 : δ * (1 / δ) = 1 := by field_simp
            linarith
        _ ≤ 1 / 2 := by
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by positivity : (0:ℝ) < 1/2)]
            linarith [Real.add_one_le_exp (1 : ℝ)]
    -- For k ≥ N: use hbound + hev
    -- For k < N: each μ_k is finite, find K_k with μ_k(Ioi K_k) ≤ ofReal ε
    -- Combine by taking max of all K values
    -- For k ≥ N: f_k(0) - f_k(δ) < ε/2
    have hlarge : ∀ k, N ≤ k →
        (μ_k k) (Set.Ioi K₀) ≤ ENNReal.ofReal ε := by
      intro k hk; haveI := hfin_k k
      have hN_bound := hN k hk
      have hK₀_bound := hbound δ K₀ hδ_pos hK₀_pos k
      have h_half : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(δ * K₀)) := by linarith
      have h_toReal : (μ_k k (Set.Ioi K₀)).toReal ≤ ε := by nlinarith
      rwa [← ENNReal.ofReal_toReal (ne_of_lt (measure_lt_top (μ_k k) _)),
        ENNReal.ofReal_le_ofReal_iff hε.le]
    -- For each k: pick K_k such that μ_k(Ioi K_k) ≤ ofReal ε (finite measure tails)
    have hfinite_K : ∀ k, ∃ K_k : ℝ,
        (μ_k k) (Set.Ioi K_k) ≤ ENNReal.ofReal ε := by
      intro k; haveI := hfin_k k
      have := tendsto_measure_iInter_atTop
        (μ := μ_k k) (s := fun (n : ℕ) => Set.Ioi (n : ℝ))
        (fun n => measurableSet_Ioi.nullMeasurableSet)
        (fun m n hmn => Set.Ioi_subset_Ioi (by exact_mod_cast hmn))
        ⟨0, measure_ne_top _ _⟩
      have hempty : ⋂ n : ℕ, Set.Ioi (n : ℝ) = ∅ := by
        ext x; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
        push_neg; exact ⟨⌈x⌉₊, Nat.le_ceil x⟩
      rw [hempty, measure_empty] at this
      rw [ENNReal.tendsto_atTop_zero] at this
      obtain ⟨M, hM⟩ := this (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
      exact ⟨M, hM M le_rfl⟩
    -- Build a single K that works for all k: take K₀ + sum of K_small for k < N
    choose K_small hK_small using hfinite_K
    refine ⟨K₀ + ∑ k ∈ Finset.range N, |K_small k|, fun k => ?_⟩
    by_cases hk : N ≤ k
    · apply le_trans (measure_mono (Set.Ioi_subset_Ioi _)) (hlarge k hk)
      have hsum_nn : 0 ≤ ∑ j ∈ Finset.range N, |K_small j| :=
        Finset.sum_nonneg (fun j _ => abs_nonneg (K_small j))
      linarith
    · push_neg at hk
      apply le_trans (measure_mono (Set.Ioi_subset_Ioi _)) (hK_small k)
      have hle_sum : |K_small k| ≤ ∑ j ∈ Finset.range N, |K_small j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (K_small j)) (Finset.mem_range.mpr hk)
      linarith [le_abs_self (K_small k)]
  -- Step 7: Prokhorov extraction
  obtain ⟨μ₀, φ, hfin_μ₀, hφ_mono, hsupp_μ₀, _, hweak⟩ :=
    finite_measure_subseq_limit (fun k => μ_k k) C
      (fun k => hfin_k k) hmass (fun k => hsupp_k k) htight
  -- Step 8: Verify Laplace identity via pointwise convergence
  refine ⟨μ₀, hfin_μ₀, hsupp_μ₀, fun t ht => ?_⟩
  -- f(t) = lim f_{φ(k)}(t) and ∫ e^{-tp} dμ_{φ(k)} → ∫ e^{-tp} dμ₀
  have h1 : Filter.Tendsto (fun k => f_k (φ k) t) Filter.atTop (nhds (f t)) :=
    (mollify_tendsto f hcont m_seq t ht).comp (StrictMono.tendsto_atTop hφ_mono)
  have h2 : Filter.Tendsto (fun k => ∫ p, Real.exp (-(t * p)) ∂(μ_k (φ k)))
      Filter.atTop (nhds (∫ p, Real.exp (-(t * p)) ∂μ₀)) :=
    tendsto_exp_integral (fun k => μ_k k) φ μ₀ hweak
      (fun k => hsupp_k k) hsupp_μ₀ t ht
  have h_eq : (fun k => f_k (φ k) t) =
      (fun k => ∫ p, Real.exp (-(t * p)) ∂(μ_k (φ k))) := by
    ext k; exact hlaplace_k (φ k) t ht
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 h2

end
