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

/-- **PD → alternating forward differences.**
For `f` semigroup-PD, `h > 0`, `t ≥ 0`:
  `(-1)^n Δ_h^n f(t) ≥ 0`

Proof: Choose `c_k = (-1)^k √C(n,k)` in the PD quadratic form.
Then `∑ᵢⱼ c̄ᵢ cⱼ f(tᵢ+tⱼ)` with `tₖ = t/2 + kh/2` gives
  `∑ᵢⱼ (-1)^{i+j} C(n,i)^{1/2} C(n,j)^{1/2} f(t + (i+j)h/2)`
which after grouping by `i+j = m` gives `(-1)^n Δ_{h/2}^n f(t)` ... no,
this needs more care with the convolution identity.

**Alternative approach** (BCR Prop. 4.2.2): Use the identity
  `(-1)^n Δ_h^n f(t) = ∑ᵢⱼ c̄ᵢ cⱼ f(sᵢ + sⱼ)`
where `c_k = (-1)^k √C(n,k)`, `s_k = t/2 + k·h`.
The PD condition gives `0 ≤ ∑ c̄ᵢcⱼ f(sᵢ+sⱼ)`.

We verify: `sᵢ + sⱼ = t + (i+j)h` and
`∑ᵢⱼ (-1)^{i+j} C(n,i)^{1/2} C(n,j)^{1/2} f(t+(i+j)h)`
= `∑_m (∑_{i+j=m} (-1)^m C(n,i)^{1/2} C(n,j)^{1/2}) f(t+mh)`
= `∑_m (-1)^m C(2n, m)^{?} f(t+mh)` ... this doesn't simplify cleanly.

**Correct approach** (Widder IV.12): Use `n+1` points with
`c_k = (-1)^k C(n,k)` (integer, not square root!) and `s_k = t/2 + k·h/2`.
Then `s_i + s_j = t + (i+j)·h/2` and the sum becomes a **convolution square**
of the binomial coefficients, which equals `(-1)^n` times the n-th forward
difference, by the Vandermonde identity. -/
lemma IsSemigroupPD.alternating_forwardDiff (hpd : IsSemigroupPD f)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (h : ℝ) (hh : 0 < h) :
    0 ≤ (-1 : ℝ) ^ n * iterForwardDiff n h f t := by
  sorry

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
  have hdiff := hpd.alternating_forwardDiff
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
