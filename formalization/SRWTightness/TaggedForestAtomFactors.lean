import SRWTightness.TaggedFixedForestLaw
import SRWTightness.TaggedBlockCounts
import Mathlib.Algebra.BigOperators.Field

open MeasureTheory
open scoped BigOperators ENNReal

namespace SRWTightness

/-- The ordered mark-atom factor of one actual tagged block. -/
noncomputable def taggedMarkAtomProduct {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₀ : Measure α) (μ₁ : Measure β) (r : Sum (List α) (List β)) : ℝ :=
  r.elim (fun rs ↦ (rs.map (fun x ↦ μ₀.real {x})).prod)
    (fun rs ↦ (rs.map (fun x ↦ μ₁.real {x})).prod)

/-- The exact positive-geometric slot weight of a prescribed natural count vector. -/
noncomputable def taggedCountVectorWeight {n : ℕ} (p : ℝ) (r : Fin n → ℕ) : ℝ :=
  ∏ i, p * (1 - p) ^ (r i - 1)

/-- Ordered mark-atom factors are nonnegative. -/
theorem tagged_mark_atom_product_nonneg {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ₀ : Measure α) (μ₁ : Measure β) (r : Sum (List α) (List β)) :
    0 ≤ taggedMarkAtomProduct μ₀ μ₁ r := by
  cases r <;> apply List.prod_nonneg <;> intro x hx
  all_goals
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact measureReal_nonneg

/-- The original geometric count-vector factor is nonnegative including parameter endpoints. -/
theorem tagged_count_vector_weight_nonneg {n : ℕ} (p : ℝ) (r : Fin n → ℕ)
    (hp : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ taggedCountVectorWeight p r := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg hp (pow_nonneg (sub_nonneg.mpr hp₁) _)

/-- Matching the actual tag and block length gives its exact ordered mark-atom product. -/
theorem tagged_fixed_forest_atom_match {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (r : Sum (List α) (List β)) :
    taggedFixedForestLaw μ₀ μ₁ (taggedBlockLabel r) (taggedBlockLength r) {r} =
      ENNReal.ofReal (taggedMarkAtomProduct μ₀ μ₁ r) := by
  cases r with
  | inl rs =>
    change taggedFixedForestLaw μ₀ μ₁ false rs.length {Sum.inl rs} =
      ENNReal.ofReal ((rs.map (fun x ↦ μ₀.real {x})).prod)
    rw [tagged_fixed_forest_left_singleton]
    exact independentForestLaw_singleton μ₀ rs.length rs rfl
  | inr rs =>
    change taggedFixedForestLaw μ₀ μ₁ true rs.length {Sum.inr rs} =
      ENNReal.ofReal ((rs.map (fun x ↦ μ₁.real {x})).prod)
    rw [tagged_fixed_forest_right_singleton]
    exact independentForestLaw_singleton μ₁ rs.length rs rfl

/-- A matching fixed-count tuple has exactly the product of all its ordered mark factors. -/
theorem tagged_fixed_forest_pi_atom_match {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (n : ℕ) (label : Fin n → Bool) (j : Fin n → ℕ)
    (r : Fin n → Sum (List α) (List β))
    (h : ∀ i, taggedBlockLabel (r i) = label i ∧ taggedBlockLength (r i) = j i) :
    (Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (j i))) {r} =
      ENNReal.ofReal (∏ i, taggedMarkAtomProduct μ₀ μ₁ (r i)) := by
  rw [Measure.pi_singleton]
  have hs (i : Fin n) : taggedFixedForestLaw μ₀ μ₁ (label i) (j i) {r i} =
      ENNReal.ofReal (taggedMarkAtomProduct μ₀ μ₁ (r i)) := by
    rw [← (h i).1, ← (h i).2]
    exact tagged_fixed_forest_atom_match μ₀ μ₁ (r i)
  simp_rw [hs]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ tagged_mark_atom_product_nonneg μ₀ μ₁ (r i))]

/-- Compatible positive block weights factor into exact count and ordered mark products. -/
theorem ordered_tagged_block_weight_factors {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ₀ : Measure α) (μ₁ : Measure β) (p : ℝ) (n : ℕ)
    (label : Fin n → Bool) (r : Fin n → Sum (List α) (List β))
    (hr : orderedTaggedCompatible label r) :
    (∏ i, (r i).elim (orderedForestBlockWeight p μ₀) (orderedForestBlockWeight p μ₁)) =
      taggedCountVectorWeight p (fun i ↦ taggedBlockLength (r i)) *
        ∏ i, taggedMarkAtomProduct μ₀ μ₁ (r i) := by
  rw [taggedCountVectorWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi := hr i
  cases hri : r i with
  | inl rs =>
    have hn : rs ≠ [] := (by simpa [hri] using hi : label i = false ∧ rs ≠ []).2
    simp [orderedForestBlockWeight, hn, taggedBlockLength, taggedMarkAtomProduct]
  | inr rs =>
    have hn : rs ≠ [] := (by simpa [hri] using hi : label i = true ∧ rs ≠ []).2
    simp [orderedForestBlockWeight, hn, taggedBlockLength, taggedMarkAtomProduct]

/-- The original restricted tuple atom has the same count/mark product without changing its
event. -/
theorem ordered_tagged_count_weight_factors {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ₀ : Measure α) (μ₁ : Measure β) (p : ℝ) (n : ℕ)
    (label : Fin n → Bool) (r : Fin n → Sum (List α) (List β))
    (hr : orderedTaggedCompatible label r) (k l : ℕ)
    (hk : (orderedTaggedForests r).1.length = k) (hl : (orderedTaggedForests r).2.length = l) :
    orderedTaggedCountWeight p label μ₀ μ₁ k l r =
      taggedCountVectorWeight p (fun i ↦ taggedBlockLength (r i)) *
        ∏ i, taggedMarkAtomProduct μ₀ μ₁ (r i) := by
  rw [orderedTaggedCountWeight, if_pos ⟨hr, hk, hl⟩]
  exact ordered_tagged_block_weight_factors μ₀ μ₁ p n label r hr

end SRWTightness
