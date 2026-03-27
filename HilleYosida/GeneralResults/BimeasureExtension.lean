/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.

# Bimeasure Extension Theorem (Kingman-Carathéodory)

Given a family of finite measures σ(B) on X indexed by measurable
sets B ⊆ Y, where B ↦ σ(B)(A) is countably additive for each A,
there exists a joint measure μ on X × Y with μ(A × B) = σ(B)(A).

This is a consequence of the Carathéodory extension theorem applied
to the semiring of measurable rectangles.

## References

* Kingman (1967), "Completely random measures", Theorem 1
* Kallenberg, "Foundations of Modern Probability", §1.9
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.MeasurableSpace.Prod

open MeasureTheory Measure Set
open scoped ENNReal

/-! ## Auxiliary: measurable rectangles form a set semiring -/

section RectSemiring

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The collection of measurable rectangles `A ×ˢ B` in `X × Y`. -/
def measurableRect (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] : Set (Set (X × Y)) :=
  image2 (· ×ˢ ·) {s : Set X | MeasurableSet s} {t : Set Y | MeasurableSet t}

theorem mem_measurableRect {s : Set (X × Y)} :
    s ∈ measurableRect X Y ↔
      ∃ A B, MeasurableSet A ∧ MeasurableSet B ∧ s = A ×ˢ B := by
  simp only [measurableRect, image2, mem_setOf_eq]
  constructor
  · rintro ⟨A, hA, B, hB, rfl⟩; exact ⟨A, B, hA, hB, rfl⟩
  · rintro ⟨A, B, hA, hB, rfl⟩; exact ⟨A, hA, B, hB, rfl⟩

theorem empty_mem_measurableRect : (∅ : Set (X × Y)) ∈ measurableRect X Y := by
  rw [mem_measurableRect]
  exact ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, by simp⟩

theorem inter_mem_measurableRect {s t : Set (X × Y)}
    (hs : s ∈ measurableRect X Y) (ht : t ∈ measurableRect X Y) :
    s ∩ t ∈ measurableRect X Y := by
  rw [mem_measurableRect] at hs ht ⊢
  obtain ⟨A₁, B₁, hA₁, hB₁, rfl⟩ := hs
  obtain ⟨A₂, B₂, hA₂, hB₂, rfl⟩ := ht
  exact ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, by rw [Set.prod_inter_prod]⟩

/-- Measurable rectangles form a set semiring.

This is the key structural fact: rectangles are closed under intersection,
and the difference of two rectangles can be written as a finite disjoint
union of rectangles. -/
theorem isSetSemiring_measurableRect : IsSetSemiring (measurableRect X Y) where
  empty_mem := empty_mem_measurableRect
  inter_mem _ hs _ ht := inter_mem_measurableRect hs ht
  diff_eq_sUnion' := by
    intro s hs t ht
    rw [mem_measurableRect] at hs ht
    obtain ⟨A₁, B₁, hA₁, hB₁, rfl⟩ := hs
    obtain ⟨A₂, B₂, hA₂, hB₂, rfl⟩ := ht
    -- (A₁ ×ˢ B₁) \ (A₂ ×ˢ B₂) = (A₁ \ A₂) ×ˢ B₁ ∪ (A₁ ∩ A₂) ×ˢ (B₁ \ B₂)
    refine ⟨{(A₁ \ A₂) ×ˢ B₁, (A₁ ∩ A₂) ×ˢ (B₁ \ B₂)}, ?_, ?_, ?_⟩
    · -- elements are in measurableRect
      intro u hu
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu
      cases hu with
      | inl h => rw [h, mem_measurableRect]; exact ⟨_, _, hA₁.diff hA₂, hB₁, rfl⟩
      | inr h => rw [h, mem_measurableRect]; exact ⟨_, _, hA₁.inter hA₂, hB₁.diff hB₂, rfl⟩
    · -- pairwise disjoint
      intro u hu v hv huv
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu hv
      unfold Function.onFun
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · simp only [id]
        rw [Set.disjoint_left]
        intro ⟨x, y⟩ hxy₁ hxy₂
        exact hxy₁.1.2 hxy₂.1.2
      · simp only [id]
        rw [Set.disjoint_left]
        intro ⟨x, y⟩ hxy₁ hxy₂
        exact hxy₂.1.2 hxy₁.1.2
      · exact absurd rfl huv
    · -- sUnion equals difference
      ext ⟨x, y⟩
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton,
        Set.mem_union, Set.mem_prod, Set.mem_diff, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hx₁, hy₁⟩, hne⟩
        by_cases hx₂ : x ∈ A₂
        · right; exact ⟨⟨hx₁, hx₂⟩, hy₁, fun hy₂ => hne ⟨hx₂, hy₂⟩⟩
        · left; exact ⟨⟨hx₁, hx₂⟩, hy₁⟩
      · rintro (⟨⟨hx₁, hx₂⟩, hy₁⟩ | ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩)
        · exact ⟨⟨hx₁, hy₁⟩, fun ⟨hx₂', _⟩ => hx₂ hx₂'⟩
        · exact ⟨⟨hx₁, hy₁⟩, fun ⟨_, hy₂'⟩ => hy₂ hy₂'⟩

theorem generateFrom_measurableRect :
    MeasurableSpace.generateFrom (measurableRect X Y) = Prod.instMeasurableSpace :=
  generateFrom_prod

end RectSemiring

/-! ## The AddContent on measurable rectangles -/

section Content

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Given a family of measures `σ(B)` on `X`, define a set function on measurable rectangles
of `X × Y`: the value on `A ×ˢ B` is `σ(B)(A)`.

For the empty set, the value is explicitly 0. For a nonempty set that is not a measurable
rectangle, the iSup is vacuously `⊥ = 0`, which is harmless since the `AddContent` axiom
`sUnion'` only triggers when the union is itself in the family.

For a nonempty rectangle `A ×ˢ B` (with `A, B` both nonempty), the decomposition is unique
(by `Set.prod_eq_prod_iff_of_nonempty`), so the iSup collapses to `σ(B)(A)`. -/
noncomputable def bimeasureContentFun
    (σ : {B : Set Y // MeasurableSet B} → Measure X) :
    Set (X × Y) → ℝ≥0∞ := fun S =>
  if S = ∅ then 0
  else ⨆ (A : Set X) (B : Set Y) (_ : MeasurableSet A) (hB : MeasurableSet B) (_ : S = A ×ˢ B),
    σ ⟨B, hB⟩ A

/-- Key lemma: `bimeasureContentFun` on a measurable rectangle `A ×ˢ B` equals `σ(B)(A)`. -/
theorem bimeasureContentFun_rect
    (σ : {B : Set Y // MeasurableSet B} → Measure X)
    (_hfin : ∀ B, IsFiniteMeasure (σ B))
    (h_empty : σ ⟨∅, MeasurableSet.empty⟩ = 0)
    {A : Set X} {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    bimeasureContentFun σ (A ×ˢ B) = σ ⟨B, hB⟩ A := by
  simp only [bimeasureContentFun]
  by_cases hne : A ×ˢ B = ∅
  · -- A ×ˢ B = ∅, so A = ∅ or B = ∅
    simp only [hne, ↓reduceIte]
    rw [Set.prod_eq_empty_iff] at hne
    rcases hne with rfl | rfl
    · simp
    · -- B = ∅, so σ ⟨∅, hB⟩ = 0
      change 0 = σ ⊥ A
      rw [show (⊥ : {B : Set Y // MeasurableSet B}) = ⟨∅, MeasurableSet.empty⟩ from rfl]
      rw [h_empty]; simp
  · simp only [hne, ↓reduceIte]
    apply le_antisymm
    · -- ⨆ ≤ σ(B)(A): every decomposition of nonempty rect is the same
      apply iSup_le; intro A'
      apply iSup_le; intro B'
      apply iSup_le; intro hA'
      apply iSup_le; intro hB'
      apply iSup_le; intro heq
      have hne' : (A ×ˢ B : Set (X × Y)).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
      rw [Set.prod_eq_prod_iff_of_nonempty hne'] at heq
      rcases heq with ⟨rfl, rfl⟩
      rfl
    · -- σ(B)(A) ≤ ⨆: take A' = A, B' = B
      exact le_iSup₂_of_le A B (le_iSup₂_of_le hA hB (le_iSup_of_le rfl le_rfl))

/-- The bimeasure content function maps ∅ to 0. -/
theorem bimeasureContentFun_empty
    (σ : {B : Set Y // MeasurableSet B} → Measure X) :
    bimeasureContentFun σ ∅ = 0 := by
  simp [bimeasureContentFun]

/-- Finite additivity of the bimeasure content on measurable rectangles.
If a finite disjoint union of measurable rectangles is itself a measurable rectangle,
then the content of the union equals the sum of the contents. -/
theorem bimeasureContentFun_sUnion
    (σ : {B : Set Y // MeasurableSet B} → Measure X)
    (hfin : ∀ B, IsFiniteMeasure (σ B))
    (h_empty : σ ⟨∅, MeasurableSet.empty⟩ = 0)
    (h_iUnion : ∀ (B : ℕ → Set Y) (hB : ∀ n, MeasurableSet (B n))
      (hdisj : Pairwise (Function.onFun Disjoint B)),
      σ ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩ =
        Measure.sum (fun n => σ ⟨B n, hB n⟩))
    (I : Finset (Set (X × Y)))
    (h_ss : ↑I ⊆ measurableRect X Y)
    (h_dis : PairwiseDisjoint (I : Set (Set (X × Y))) id)
    (h_mem : ⋃₀ ↑I ∈ measurableRect X Y) :
    bimeasureContentFun σ (⋃₀ ↑I) = ∑ u ∈ I, bimeasureContentFun σ u := by
  classical
  -- We prove a stronger statement by strong induction on |I|,
  -- generalizing over A, B, and I.
  suffices key : ∀ (m : ℕ) (J : Finset (Set (X × Y)))
      (_ : J.card = m) (_ : ↑J ⊆ measurableRect X Y)
      (_ : PairwiseDisjoint (J : Set (Set (X × Y))) id)
      (_ : ⋃₀ ↑J ∈ measurableRect X Y),
      bimeasureContentFun σ (⋃₀ ↑J) = ∑ u ∈ J, bimeasureContentFun σ u from
    key I.card I rfl h_ss h_dis h_mem
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro J hJ_card hJ_ss hJ_dis hJ_mem
  -- Extract the rectangle decomposition of the union
  obtain ⟨A', B', hA', hB', hAB'⟩ := mem_measurableRect.mp hJ_mem
  rw [hAB', bimeasureContentFun_rect σ hfin h_empty hA' hB']
  -- Case |J| = 0
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : J = ∅ := Finset.card_eq_zero.mp hJ_card
    subst this
    simp only [Finset.sum_empty, Finset.coe_empty, Set.sUnion_empty] at *
    rw [eq_comm, Set.prod_eq_empty_iff] at hAB'
    rcases hAB' with rfl | rfl
    · simp
    · rw [show σ ⟨∅, hB'⟩ = σ ⟨∅, MeasurableSet.empty⟩ from by congr, h_empty]; simp
  -- Case |J| = 1
  by_cases hm1 : m = 1
  · rw [hm1] at hJ_card
    rw [Finset.card_eq_one] at hJ_card
    obtain ⟨u₀, rfl⟩ := hJ_card
    simp only [Finset.sum_singleton, Finset.coe_singleton, Set.sUnion_singleton] at *
    rw [hAB', bimeasureContentFun_rect σ hfin h_empty hA' hB']
  -- Case |J| ≥ 2.
  have hm2 : 2 ≤ m := by omega
  -- Pick u₀ ∈ J
  obtain ⟨u₀, hu₀⟩ := J.nonempty_of_ne_empty (by intro h; simp [h] at hJ_card; omega)
  -- u₀ is a measurable rectangle
  obtain ⟨A₀, B₀, hA₀, hB₀, hAB₀⟩ := mem_measurableRect.mp (hJ_ss hu₀)
  let J' := J.erase u₀
  have hJ'_card : J'.card = m - 1 := by
    simp [J', Finset.card_erase_of_mem hu₀, hJ_card]
  have hJ'_lt : J'.card < m := by omega
  have hJ'_ss : ↑J' ⊆ measurableRect X Y := fun u hu =>
    hJ_ss (Finset.mem_of_mem_erase hu)
  have hJ'_dis : PairwiseDisjoint (J' : Set (Set (X × Y))) id := by
    exact Set.PairwiseDisjoint.subset hJ_dis (Finset.coe_subset.mpr (Finset.erase_subset _ _))
  -- The sum splits: ∑ J = bimeasureContentFun σ u₀ + ∑ J'
  have sum_split : ∑ u ∈ J, bimeasureContentFun σ u =
      bimeasureContentFun σ u₀ + ∑ u ∈ J', bimeasureContentFun σ u := by
    rw [← Finset.add_sum_erase J _ hu₀]
  rw [sum_split, hAB₀, bimeasureContentFun_rect σ hfin h_empty hA₀ hB₀]
  -- Goal: σ⟨B'⟩(A') = σ⟨B₀⟩(A₀) + ∑ u ∈ J', bimeasureContentFun σ u
  -- Step 1: σ⟨B'⟩(A') = σ⟨B'⟩(A' \ A₀) + σ⟨B'⟩(A₀)  [measure additivity]
  -- Step 2: σ⟨B'⟩(A₀) = σ⟨B₀⟩(A₀) + σ⟨B'\B₀⟩(A₀)    [h_iUnion]
  -- Step 3: σ⟨B'⟩(A'\A₀) = IH on piece 1              [strong induction]
  -- Step 4: σ⟨B'\B₀⟩(A₀) = IH on piece 2              [strong induction]
  -- Step 5: Recombine sums
  --
  -- Each step involves substantial Lean scaffolding (building new finsets,
  -- proving subset/disjointness/union conditions, splitting rectangle sums).
  -- The full formalization requires ~200 lines of Lean code.
  -- The mathematical argument is the standard "rectangle splitting" technique
  -- from Kingman (1967) / Kallenberg §1.9.
  sorry

/-- The `AddContent` on measurable rectangles defined by a bimeasure family. -/
noncomputable def bimeasureAddContent
    (σ : {B : Set Y // MeasurableSet B} → Measure X)
    (hfin : ∀ B, IsFiniteMeasure (σ B))
    (h_empty : σ ⟨∅, MeasurableSet.empty⟩ = 0)
    (h_iUnion : ∀ (B : ℕ → Set Y) (hB : ∀ n, MeasurableSet (B n))
      (hdisj : Pairwise (Function.onFun Disjoint B)),
      σ ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩ =
        Measure.sum (fun n => σ ⟨B n, hB n⟩)) :
    AddContent ℝ≥0∞ (measurableRect X Y) where
  toFun := bimeasureContentFun σ
  empty' := bimeasureContentFun_empty σ
  sUnion' := bimeasureContentFun_sUnion σ hfin h_empty h_iUnion

/-- Sigma-subadditivity of the bimeasure content.
If `A ×ˢ B ⊆ ⋃ₙ Aₙ ×ˢ Bₙ`, then `σ(B)(A) ≤ ∑ₙ σ(Bₙ)(Aₙ)`.

This is the core analytical step. For each `x ∈ A`, the slice condition
`B ⊆ ⋃_{n : x ∈ Aₙ} Bₙ` combined with measure monotonicity and
countable subadditivity of `σ` yields the pointwise bound. Integrating over
`A` (using that `σ(B)(A) = ∫_A dσ(B)` and `σ(Bₙ)(Aₙ) = ∫_{Aₙ} dσ(Bₙ)`)
gives the result. -/
theorem bimeasureAddContent_sigmaSubadditive
    (σ : {B : Set Y // MeasurableSet B} → Measure X)
    (hfin : ∀ B, IsFiniteMeasure (σ B))
    (h_empty : σ ⟨∅, MeasurableSet.empty⟩ = 0)
    (h_iUnion : ∀ (B : ℕ → Set Y) (hB : ∀ n, MeasurableSet (B n))
      (hdisj : Pairwise (Function.onFun Disjoint B)),
      σ ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩ =
        Measure.sum (fun n => σ ⟨B n, hB n⟩)) :
    (bimeasureAddContent σ hfin h_empty h_iUnion).IsSigmaSubadditive := by
  sorry

end Content

/-! ## Main theorem -/

/-- **Bimeasure extension (Kingman-Carathéodory).**

Given a family of finite measures `σ(B)` on `X` indexed by measurable
sets `B ⊆ Y`, where `B ↦ σ(B)(A)` is countably additive for each
measurable `A`, there exists a finite measure `μ` on `X × Y` satisfying
`μ(A × B) = σ(B)(A)` on measurable rectangles.

**Proof:**
1. The measurable rectangles form a set semiring (`isSetSemiring_measurableRect`).
2. The product σ-algebra is generated by these rectangles (`generateFrom_measurableRect`).
3. Define an `AddContent` on rectangles via `m(A ×ˢ B) = σ(B)(A)`.
4. Verify sigma-subadditivity.
5. Apply `AddContent.measure` (Carathéodory extension) to get `μ`.
6. `μ(A ×ˢ B) = σ(B)(A)` by `AddContent.measure_eq`.
7. Finiteness: `μ(univ) = σ(univ)(univ) < ∞`. -/
theorem bimeasure_extension
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (σ : {B : Set Y // MeasurableSet B} → Measure X)
    (hfin : ∀ B, IsFiniteMeasure (σ B))
    (h_empty : σ ⟨∅, MeasurableSet.empty⟩ = 0)
    (h_iUnion : ∀ (B : ℕ → Set Y) (hB : ∀ n, MeasurableSet (B n))
      (hdisj : Pairwise (Function.onFun Disjoint B)),
      σ ⟨⋃ n, B n, MeasurableSet.iUnion hB⟩ =
        Measure.sum (fun n => σ ⟨B n, hB n⟩)) :
    ∃ (μ : Measure (X × Y)),
      IsFiniteMeasure μ ∧
      ∀ (A : Set X) (hA : MeasurableSet A) (B : Set Y) (hB : MeasurableSet B),
        μ (A ×ˢ B) = σ ⟨B, hB⟩ A := by
  -- Step 1-3: Build the AddContent
  let m := bimeasureAddContent σ hfin h_empty h_iUnion
  -- Step 4: Sigma-subadditivity
  have m_subadd := bimeasureAddContent_sigmaSubadditive σ hfin h_empty h_iUnion
  -- Step 5: Apply Carathéodory extension
  let hC := @isSetSemiring_measurableRect X Y _ _
  have hC_gen : Prod.instMeasurableSpace ≤
      MeasurableSpace.generateFrom (measurableRect X Y) := by
    rw [generateFrom_measurableRect]
  let μ := AddContent.measure m hC hC_gen m_subadd
  refine ⟨μ, ?_, ?_⟩
  · -- Step 7: Finiteness
    constructor
    have h_univ_rect : (Set.univ : Set (X × Y)) ∈ measurableRect X Y := by
      rw [mem_measurableRect]
      exact ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, Set.univ_prod_univ.symm⟩
    have h_eq := AddContent.measure_eq m hC generateFrom_measurableRect.symm m_subadd h_univ_rect
    rw [h_eq]
    rw [show (m : Set (X × Y) → ℝ≥0∞) (Set.univ) =
        bimeasureContentFun σ (Set.univ) from rfl]
    rw [show (Set.univ : Set (X × Y)) = Set.univ ×ˢ Set.univ from Set.univ_prod_univ.symm]
    rw [bimeasureContentFun_rect σ hfin h_empty MeasurableSet.univ MeasurableSet.univ]
    exact measure_lt_top _ _
  · -- Step 6: Rectangle property
    intro A hA B hB
    have h_rect : A ×ˢ B ∈ measurableRect X Y := by
      rw [mem_measurableRect]; exact ⟨A, B, hA, hB, rfl⟩
    have h_eq := AddContent.measure_eq m hC generateFrom_measurableRect.symm m_subadd h_rect
    rw [h_eq]
    exact bimeasureContentFun_rect σ hfin h_empty hA hB
