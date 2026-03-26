/-
Temporary test file to verify trig_poly_integral_pd proof compiles.
-/

import HilleYosida.SemigroupGroupExtension
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory Complex Set Filter Finset

private lemma trig_poly_integral_pd {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (n : ℕ) (c : Fin n → ℂ) (ts : Fin n → ℝ) (hts : ∀ i, 0 ≤ ts i)
    (m : ℕ) (dd : Fin m → ℂ) (as : Fin m → (Fin d → ℝ)) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      star (c i) * c j *
        ↑(∫ q : Fin d → ℝ,
            (Complex.normSq (∑ k : Fin m, dd k *
              exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
          ∂(ν (ts i + ts j)))).re := by
  -- Step 1: Apply IsSemigroupGroupPD with n·m product test points
  -- indexed by Fin (n * m) via finProdFinEquiv.
  let e := finProdFinEquiv (m := n) (n := m)
  let c' : Fin (n * m) → ℂ := fun p => c (e.symm p).1 * dd (e.symm p).2
  let ts' : Fin (n * m) → ℝ := fun p => ts (e.symm p).1
  let as' : Fin (n * m) → (Fin d → ℝ) := fun p => as (e.symm p).2
  have hts' : ∀ p, 0 ≤ ts' p := fun p => hts _
  have hPD := (hpd (n * m) c' ts' as' hts').2
  -- Step 2: Show target = PD sum (which is ≥ 0).
  -- We prove: target.re = (quadruple sum over Fin n × Fin m).re = PD sum.re ≥ 0
  suffices heq : ∀ i j : Fin n,
      star (c i) * c j *
        ↑(∫ q : Fin d → ℝ,
            (Complex.normSq (∑ k : Fin m, dd k *
              exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
          ∂(ν (ts i + ts j))) =
      star (c i) * c j *
        ∑ k : Fin m, ∑ l : Fin m,
          star (dd k) * dd l * F (ts i + ts j) (as l - as k) by
    -- Show target = PD sum
    have h_target_eq : (∑ i : Fin n, ∑ j : Fin n,
        star (c i) * c j *
          ↑(∫ q : Fin d → ℝ,
              (Complex.normSq (∑ k : Fin m, dd k *
                exp (I * ↑(∑ l : Fin d, q l * (as k) l))) : ℝ)
            ∂(ν (ts i + ts j)))).re =
      (∑ i : Fin n, ∑ k : Fin m, ∑ j : Fin n, ∑ l : Fin m,
        star (c i) * star (dd k) * (c j * dd l) *
          F (ts i + ts j) (as l - as k)).re := by
      congr 1
      congr 1; ext i; congr 1; ext j
      rw [heq]
      simp_rw [← Finset.mul_sum]; ring
    rw [h_target_eq]
    -- Now show this quadruple sum = PD sum (via reindexing)
    have h_pd_eq : (∑ i : Fin n, ∑ k : Fin m,
        ∑ j : Fin n, ∑ l : Fin m,
          star (c i) * star (dd k) * (c j * dd l) *
            F (ts i + ts j) (as l - as k)).re =
      (∑ p : Fin (n * m), ∑ q : Fin (n * m),
        star (c' p) * c' q *
          F (ts' p + ts' q) (as' q - as' p)).re := by
      congr 1
      -- Reindex using finProdFinEquiv
      rw [← Fintype.sum_prod_type']
      rw [← e.sum_comp]
      congr 1; ext p
      rw [← Fintype.sum_prod_type']
      rw [← e.sum_comp]
      congr 1; ext q
      simp only [c', ts', as', star_mul, e.symm_apply_apply]
      ring
    rw [h_pd_eq]
    exact hPD
  -- Step 3: Prove heq — the inner double sum equals the integral of normSq
  intro i j
  congr 1
  have ht_ij : 0 ≤ ts i + ts j := add_nonneg (hts i) (hts j)
  haveI : IsFiniteMeasure (ν (ts i + ts j)) := hν _ ht_ij
  -- Substitute hνF into the RHS
  simp_rw [hνF _ ht_ij]
  -- Each integrand is bounded hence integrable
  have hint : ∀ k l, Integrable (fun q : Fin d → ℝ =>
      star (dd k) * dd l *
        exp (I * ↑(∑ r : Fin d, q r * (as l - as k) r)))
      (ν (ts i + ts j)) := by
    intro k l
    apply Integrable.const_mul
    apply (integrable_const (1 : ℂ)).mono
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · exact ae_of_all _ (fun q => by simp [norm_exp_I])
  -- Pull the double sum inside the integral
  symm
  rw [show ∑ k : Fin m, ∑ l : Fin m,
      star (dd k) * dd l *
        ∫ q, exp (I * ↑(∑ r : Fin d, q r * (as l - as k) r))
          ∂(ν (ts i + ts j)) =
    ∫ q, ∑ k : Fin m, ∑ l : Fin m,
      star (dd k) * dd l *
        exp (I * ↑(∑ r : Fin d, q r * (as l - as k) r))
      ∂(ν (ts i + ts j)) from by
    symm
    rw [integral_finset_sum _ (fun k _ =>
      integrable_finset_sum _ (fun l _ => hint k l))]
    congr 1; ext k
    rw [integral_finset_sum _ (fun l _ => hint k l)]
    congr 1; ext l
    exact integral_const_mul _ _]
  -- Pointwise: ∑_k ∑_l d̄_k d_l e^{i⟨as_l-as_k, q⟩} = normSq(∑ d_k e^{i⟨as_k, q⟩})
  congr 1; ext q
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul]
  rw [Finset.sum_mul]
  push_cast
  congr 1; ext k
  rw [Finset.mul_sum]
  congr 1; ext l
  simp only [star_mul]
  have hstar_exp : ∀ (r : ℝ), star (exp (I * ↑r)) =
      exp (-(I * ↑r)) := by
    intro r
    rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl,
        ← Complex.exp_conj, map_mul, Complex.conj_I,
        Complex.conj_ofReal, neg_mul]
  rw [hstar_exp, ← Complex.exp_add]
  congr 1
  · ring
  · push_cast
    simp only [Pi.sub_apply, Complex.ofReal_sub]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring

end
