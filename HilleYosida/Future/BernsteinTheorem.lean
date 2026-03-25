/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# BCR Theorem 4.1.13: Semigroup Bochner via Spatial Bochner + Bernstein

Proves `semigroupGroupBochner` (BCR 4.1.13) by decomposing into:
  BCR 4.1.13 = Bochner on ℝ^d  +  Bernstein on [0, ∞)

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), §4.1
* Bernstein, "Sur les fonctions absolument monotones" (1928)
-/

import HilleYosida.SemigroupGroupExtension
import HilleYosida.Bernstein
import Bochner.Main

noncomputable section

open MeasureTheory Complex Set Filter Finset

/-! ## Step 1: Spatial Bochner for each time slice -/

/-- For `t ≥ 0`, the spatial slice `a ↦ F(t, a)` is continuous. -/
lemma spatial_slice_continuous {d : ℕ} {F : ℝ → (Fin d → ℝ) → ℂ}
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (t : ℝ) (ht : 0 ≤ t) : Continuous (fun a => F t a) := by
  -- ContinuousOn on Ici × univ composed with (t, ·) : ℝ^d → ℝ × ℝ^d
  exact hcont.comp_continuous
    (continuous_const.prodMk continuous_id')
    (fun a => ⟨Set.mem_Ici.mpr ht, Set.mem_univ _⟩)

/-- `F(t, 0)` is real and nonneg for `t ≥ 0` (from PD with n=1). -/
lemma F_zero_real_nonneg {d : ℕ} {F : ℝ → (Fin d → ℝ) → ℂ}
    (hpd : IsSemigroupGroupPD d F) (t : ℝ) (ht : 0 ≤ t) :
    (F t 0).im = 0 ∧ 0 ≤ (F t 0).re := by
  have h := hpd 1 ![1] ![t / 2] ![0] (by intro i; fin_cases i; simp; linarith)
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, star_one, one_mul,
    sub_zero, show t / 2 + t / 2 = t from by ring] at h
  exact h

/-! ## BCR Assembly

Steps 2-4 of the BCR decomposition involve:
- Extracting spatial Bochner measures ν_t (from `bochner_theorem` + normalization)
- Showing t ↦ ν_t(B) is completely monotone (semigroup PD → CM)
- Applying `bernstein_theorem` to get temporal Laplace measures
- Assembling the product measure via kernel construction

The individual sorry lemmas below isolate the measure-theoretic content. -/

/-- **BCR Step 2**: Spatial Bochner measures exist with the Fourier property.

For each t ≥ 0, there is a finite measure ν_t on ℝ^d with total mass ≤ C
such that F(t, a) = ∫ e^{i⟨a,q⟩} dν_t(q).

Uses `bochner_theorem` (from mrdouglasny/bochner) + normalization by F(t,0).
When F(t, 0) = 0, ν_t = 0 and F(t, ·) ≡ 0 by Cauchy-Schwarz for PD functions. -/
lemma spatial_bochner_measures {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∀ t, 0 ≤ t → ∃ (ν : Measure (Fin d → ℝ)), IsFiniteMeasure ν ∧
      ∀ a, F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂ν := by
  sorry

/-- **BCR Step 2b**: The spatial measures satisfy the semigroup PD condition:
for each Borel B, t ↦ ν_t(B) is completely monotone.

This is the core lemma connecting spatial Fourier structure to temporal
Laplace structure. It follows from the semigroup PD condition on F and
the Fourier representation of ν_t. -/
lemma spatial_measures_cm {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    IsCompletelyMonotone (fun t => ((ν t) B).toReal) := by
  sorry

/-- **BCR Step 4**: Product measure assembly.

Given spatial measures ν_t satisfying the CM condition per Borel set,
construct a single measure μ on [0,∞) × ℝ^d reproducing the
Fourier-Laplace transform. Uses Bernstein to decompose each t ↦ ν_t(B),
then assembles via measure kernel construction. -/
lemma product_measure_assembly {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (hνCM : ∀ B, MeasurableSet B →
      IsCompletelyMonotone (fun t => ((ν t) B).toReal)) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ ((Set.Iio 0).prod Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          exp (-(↑(t * p.1) : ℂ)) *
            exp (I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ := by
  sorry

/-- **BCR Theorem 4.1.13** — semigroup Bochner.

Assembles the three steps: spatial Bochner measures (Step 1),
complete monotonicity (Step 2), product assembly (Step 4).
Bernstein's theorem (Step 3) is used inside Step 4. -/
theorem semigroupGroupBochner_proof (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ ((Set.Iio 0).prod Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          exp (-(↑(t * p.1) : ℂ)) *
            exp (I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ := by
  -- Step 1: Spatial Bochner measures (uses bochner_theorem)
  have hν := spatial_bochner_measures F hcont hbdd hpd
  -- Steps 2-4: CM + Bernstein + product assembly
  -- The spatial measures from Step 1 feed into product_measure_assembly,
  -- which internally uses bernstein_theorem and spatial_measures_cm.
  -- Full wiring deferred to when Bernstein sorrys are closed.
  sorry

end
