import SRWTightness.GeometricMarkedListLaw
import SRWTightness.TaggedFixedForestLaw
import SRWTightness.TaggedBlockCounts

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- A fixed tagged forest atom vanishes unless both its prescribed tag and root count match. -/
theorem tagged_fixed_forest_atom_zero_unless {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) (c : Bool) (j : ℕ) (r : Sum (List α) (List β))
    (h : ¬ (taggedBlockLabel r = c ∧ taggedBlockLength r = j)) :
    taggedFixedForestLaw μ₀ μ₁ c j {r} = 0 := by
  cases c with
  | false =>
    cases r with
    | inl rs =>
      rw [tagged_fixed_forest_left_singleton]
      apply independentForestLaw_singleton_wrong_length
      intro hlen
      exact h ⟨rfl, hlen⟩
    | inr rs => exact tagged_fixed_forest_left_wrong_tag μ₀ μ₁ j rs
  | true =>
    cases r with
    | inl rs => exact tagged_fixed_forest_right_wrong_tag μ₀ μ₁ j rs
    | inr rs =>
      rw [tagged_fixed_forest_right_singleton]
      apply independentForestLaw_singleton_wrong_length
      intro hlen
      exact h ⟨rfl, hlen⟩

/-- An independent tagged tuple atom vanishes if any of its prescribed coordinates fails. -/
theorem tagged_fixed_forest_pi_atom_zero_unless {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (n : ℕ) (label : Fin n → Bool) (j : Fin n → ℕ)
    (r : Fin n → Sum (List α) (List β))
    (h : ¬ ∀ i, taggedBlockLabel (r i) = label i ∧ taggedBlockLength (r i) = j i) :
    (Measure.pi (fun i ↦ taggedFixedForestLaw μ₀ μ₁ (label i) (j i))) {r} = 0 := by
  classical
  rw [Measure.pi_singleton]
  obtain ⟨i, hi⟩ := not_forall.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (tagged_fixed_forest_atom_zero_unless μ₀ μ₁ (label i) (j i) (r i) hi)

end SRWTightness
