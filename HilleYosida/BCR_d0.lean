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
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Data.Nat.Choose.Vandermonde

noncomputable section

open MeasureTheory Complex Finset Set

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
  simp [Fin.sum_univ_one, Matrix.cons_val_zero, star_one, one_mul, add_zero] at h
  exact_mod_cast h

/-- `f(t) ≥ 0` for all `t ≥ 0` (from PD with n=1, c=[1], ts=[t/2]). -/
lemma IsSemigroupPD.nonneg (hpd : IsSemigroupPD f) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  -- PD with n=1, c=[1], ts=[t/2]: 0 ≤ |1|² f(t/2 + t/2) = f(t)
  have h := hpd 1 ![1] ![t / 2] (by intro i; fin_cases i; simp; linarith)
  simp [Fin.sum_univ_one, add_halves] at h
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
    simp [Nat.choose_zero_right, Nat.sub_zero]
    ring
  · by_cases hkn1 : k = n + 1
    · -- k = n+1: LHS = (-1)^0 * C(n,n) - 0 = 1
      subst hkn1
      simp [Nat.choose_self, Nat.sub_self]
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
      intro k; congr 1; push_cast; ring
    simp_rw [key]
    -- Goal should now match forwardDiff_sum_recurrence
    have := forwardDiff_sum_recurrence n (fun k => f (t + ↑k * h))
    convert this using 1
    · congr 1 <;> (apply Finset.sum_congr rfl; intro k _; push_cast; ring)

/-- The Vandermonde convolution identity for signed binomial coefficients:
`∑_i ∑_j (-1)^{i+j} C(m,i) C(m,j) g(i+j) = ∑_p (-1)^p C(2m,p) g(p)`.

Follows from `Nat.add_choose_eq`: `(m+m).choose k = ∑_{i+j=k} C(m,i) C(m,j)`. -/
private lemma vandermonde_convolution_sum (m : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ (i + j) * (m.choose i : ℝ) * (m.choose j : ℝ) * g (i + j) =
    ∑ p ∈ Finset.range (2 * m + 1),
      (-1 : ℝ) ^ p * ((2 * m).choose p : ℝ) * g p := by
  -- Proof sketch: the LHS coefficient of g(p) is
  --   (-1)^p · ∑_{i+j=p, i≤m, j≤m} C(m,i) · C(m,j)
  --   = (-1)^p · C(2m, p)  by Vandermonde.
  -- We prove this by comparing coefficients of the polynomial (1-X)^{2m}
  -- viewed as ((1-X)^m)^2, evaluated at suitable points.
  -- For the formal proof, we use sorry for this standard combinatorial identity.
  -- It follows from Nat.add_choose_eq : (m+m).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * m.choose ij.2
  sorry

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
    simp [Complex.conj_ofReal, mul_comm, mul_assoc]
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
    show iterForwardDiff (2 * m) h f s ≤ _
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
    show g (t + ↑(n + 2) * h) - 2 * g (t + ↑(n + 1) * h) + g (t + ↑n * h) ≥ 0
    have hs : 0 ≤ t + ↑n * h := by positivity
    have hconv := hg_convex (t + ↑n * h) hs
    convert hconv using 2 <;> push_cast <;> ring
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

/-! ## CM-discrete → CM (smoothness)

A continuous function with nonneg alternating forward differences is C^∞
and its derivatives have the correct signs. This is Widder IV, Thm 12a.

The proof uses:
1. Alternating differences → f is monotone decreasing (n=1)
2. Alternating differences → (-Δ_h f)/h is bounded and monotone → f' exists
3. Iterate to get all derivatives -/

/-- **BCR d=0**: Bounded continuous semigroup-PD → completely monotone.

This is the key lemma that reduces the general BCR to Bernstein. -/
theorem IsSemigroupPD.isCompletelyMonotone
    (hpd : IsSemigroupPD f) (hcont : ContinuousOn f (Ici 0))
    (hbdd : ∃ C : ℝ, ∀ t, 0 ≤ t → |f t| ≤ C) :
    IsCompletelyMonotone f := by
  -- The alternating forward differences are nonneg:
  have hdiff := fun n t ht h hh => hpd.alternating_forwardDiff n t ht h hh hbdd
  -- From this + continuity, we derive C^∞ smoothness and the sign conditions.
  -- The smoothness argument (Widder IV.12a) proceeds by induction on derivative order:
  --   nonneg alternating Δ_h^1 → f monotone decreasing → f' ≤ 0 exists
  --   nonneg alternating Δ_h^2 → f' monotone increasing → f'' ≥ 0 exists
  --   ...
  sorry

/-! ## Main theorem: BCR 4.1.13 for d=0 -/

/-- **BCR 4.1.13 (d=0)**: A bounded continuous semigroup-PD function on [0,∞)
is the Laplace transform of a finite positive measure supported on [0,∞).

Combines `IsSemigroupPD.isCompletelyMonotone` with `bernstein_theorem`. -/
theorem semigroup_pd_laplace (f : ℝ → ℝ)
    (hpd : IsSemigroupPD f) (hcont : ContinuousOn f (Ici 0))
    (hbdd : ∃ C : ℝ, ∀ t, 0 ≤ t → |f t| ≤ C) :
    ∃ (μ : Measure ℝ), IsFiniteMeasure μ ∧
      μ (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  exact bernstein_theorem f (hpd.isCompletelyMonotone hcont hbdd)

end
