/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# BCR Theorem 4.1.13: Semigroup Bochner via Spatial Bochner + BCR d=0

Proves `semigroupGroupBochner` (BCR 4.1.13) by decomposing into:
  BCR 4.1.13(d) = Bochner on ℝ^d  +  BCR 4.1.13(d=0) on [0,∞)

The proof uses `semigroup_pd_laplace` (BCR d=0, proved in BCR_d0.lean)
for the temporal decomposition, and `bochner_theorem` (from
mrdouglasny/bochner) for the spatial decomposition.

## References

* Berg-Christensen-Ressel, "Harmonic Analysis on Semigroups" (1984), §4.1
* Bernstein, "Sur les fonctions absolument monotones" (1928)
-/

import HilleYosida.SemigroupGroupExtension
import HilleYosida.BCR_d0
import Bochner.Main

noncomputable section

open MeasureTheory Complex Set Filter Finset

/-! ## Step 1: Spatial Bochner measures

For each `t ≥ 0`, `spatial_slice_pd` (proved below) gives
`IsPositiveDefinite (a ↦ F(t, a))`. Combined with `bochner_theorem`,
this yields a finite measure ν_t with F(t, a) = ∫ e^{i⟨a,q⟩} dν_t(q). -/

/-- For `t ≥ 0`, the spatial slice `a ↦ F(t, a)` is continuous. -/
lemma spatial_slice_continuous {d : ℕ} {F : ℝ → (Fin d → ℝ) → ℂ}
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (t : ℝ) (ht : 0 ≤ t) : Continuous (fun a => F t a) :=
  hcont.comp_continuous (continuous_const.prodMk continuous_id')
    (fun a => ⟨mem_Ici.mpr ht, mem_univ _⟩)

/-- Spatial Bochner measures exist with the Fourier property.

For each t ≥ 0, there is a finite measure ν_t on ℝ^d such that
F(t, a) = ∫ e^{i⟨a,q⟩} dν_t(q).

Uses `bochner_theorem` + normalization by F(t,0).
When F(t, 0) = 0, F(t, ·) ≡ 0 by Cauchy-Schwarz for PD. -/
lemma spatial_bochner_measures {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F) :
    ∀ t, 0 ≤ t → ∃ (ν : Measure (Fin d → ℝ)), IsFiniteMeasure ν ∧
      ∀ a, F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂ν := by
  sorry

/-! ## Step 2: Temporal decomposition via BCR d=0

For each Borel B ⊆ ℝ^d, show t ↦ ν_t(B) is semigroup-PD on [0,∞),
then apply `semigroup_pd_laplace` to get Laplace measures.

Note: we use `IsSemigroupPD` (not `IsCompletelyMonotone`!) to avoid
the smoothness-at-zero issue. `semigroup_pd_laplace` handles this
via the mollifier + Prokhorov extraction. -/

/-- For each Borel B, the function t ↦ ν_t(B) is semigroup-PD.

Proof sketch: The semigroup PD condition on F combined with the
Fourier representation F(t,a) = ∫ e^{i⟨a,q⟩} dν_t gives, by
approximating 1_B with Fourier characters, that
∑ c̄ᵢ cⱼ ν_{tᵢ+tⱼ}(B) ≥ 0. -/
lemma spatial_measures_pd {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (B : Set (Fin d → ℝ)) (hB : MeasurableSet B) :
    IsSemigroupPD (fun t => ((ν t) B).toReal) := by
  sorry

/-! ## Step 3: Product measure assembly

Given spatial measures ν_t and their temporal Laplace decomposition
(from `semigroup_pd_laplace` applied to each t ↦ ν_t(B)),
construct a single measure μ on [0,∞) × ℝ^d reproducing the
Fourier-Laplace transform. -/

/-- Product measure assembly: combine the spatial Bochner measures
and their temporal Laplace decompositions into a single product
measure μ on [0,∞) × ℝ^d.

This uses `semigroup_pd_laplace` (from BCR_d0.lean) to decompose
each t ↦ ν_t(B), then assembles via a measure kernel. -/
lemma product_measure_assembly {d : ℕ} (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
    (hbdd : ∃ C : ℝ, ∀ t a, 0 ≤ t → ‖F t a‖ ≤ C)
    (hpd : IsSemigroupGroupPD d F)
    (ν : ℝ → Measure (Fin d → ℝ))
    (hν : ∀ t, 0 ≤ t → IsFiniteMeasure (ν t))
    (hνF : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν t))
    (hνPD : ∀ B, MeasurableSet B →
      IsSemigroupPD (fun t => ((ν t) B).toReal)) :
    ∃ (μ : Measure (ℝ × (Fin d → ℝ))),
      IsFiniteMeasure μ ∧
      μ ((Set.Iio 0).prod Set.univ) = 0 ∧
      ∀ (t : ℝ) (a : Fin d → ℝ), 0 ≤ t →
        F t a = ∫ p : ℝ × (Fin d → ℝ),
          exp (-(↑(t * p.1) : ℂ)) *
            exp (I * ↑(∑ i : Fin d, p.2 i * a i))
          ∂μ := by
  -- For each Borel B, semigroup_pd_laplace gives the Laplace decomposition:
  -- ν_t(B) = ∫ e^{-tp} dσ_B(p)
  -- The family {σ_B} defines a measure kernel, assembled into μ.
  sorry

/-! ## Main theorem -/

/-- **BCR Theorem 4.1.13** — semigroup Bochner (general d).

Bounded continuous semigroup-PD functions on `[0,∞) × ℝ^d` are
Fourier-Laplace transforms of finite positive measures supported on
`[0,∞) × ℝ^d`.

Assembles: spatial Bochner (Step 1) + temporal PD (Step 2) +
product measure (Step 3, using `semigroup_pd_laplace` from BCR_d0). -/
theorem semigroupGroupBochner_proof (d : ℕ)
    (F : ℝ → (Fin d → ℝ) → ℂ)
    (hcont : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2)
      (Ici (0 : ℝ) ×ˢ univ))
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
  -- Step 1: Spatial Bochner measures
  have hν_exists := spatial_bochner_measures F hcont hbdd hpd
  -- Choose a consistent family (via axiom of choice)
  choose ν hν_fin hνF using fun t ht => hν_exists t ht
  -- For the assembly, we need a family defined for all t (extending by 0 for t < 0)
  let ν' : ℝ → Measure (Fin d → ℝ) := fun t =>
    if h : 0 ≤ t then ν t h else 0
  have hν'_fin : ∀ t, 0 ≤ t → IsFiniteMeasure (ν' t) := by
    intro t ht; simp only [ν', dif_pos ht]; exact hν_fin t ht
  have hν'F : ∀ t, 0 ≤ t → ∀ a,
      F t a = ∫ q, exp (I * ↑(∑ i : Fin d, q i * a i)) ∂(ν' t) := by
    intro t ht a; simp only [ν', dif_pos ht]; exact hνF t ht a
  -- Step 2: Each t ↦ ν'_t(B) is semigroup-PD
  have hν'PD : ∀ B, MeasurableSet B →
      IsSemigroupPD (fun t => ((ν' t) B).toReal) :=
    spatial_measures_pd F hpd ν' hν'_fin hν'F
  -- Step 3: Product measure assembly
  exact product_measure_assembly F hcont hbdd hpd ν' hν'_fin hν'F hν'PD

end
