import SRWTightness.OrderedTaggedForestMixture

open MeasureTheory

namespace SRWTightness

/-- One independently marked fixed-size forest placed in its prescribed chronological site tag. -/
noncomputable def taggedFixedForestLaw {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) (c : Bool) (j : ℕ) : Measure (Sum (List α) (List β)) :=
  match c with
  | false => (independentForestLaw μ₀ j).map Sum.inl
  | true => (independentForestLaw μ₁ j).map Sum.inr

/-- Each prescribed-tag fixed-size forest kernel is an actual probability law. -/
instance tagged_fixed_forest_probability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (c : Bool) (j : ℕ) : IsProbabilityMeasure (taggedFixedForestLaw μ₀ μ₁ c j) := by
  cases c with
  | false => exact Measure.isProbabilityMeasure_map measurable_inl.aemeasurable
  | true => exact Measure.isProbabilityMeasure_map measurable_inr.aemeasurable

/-- A left-tagged kernel retains exactly the left independent forest atom. -/
theorem tagged_fixed_forest_left_singleton {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) (j : ℕ) (rs : List α) :
    taggedFixedForestLaw μ₀ μ₁ false j {Sum.inl rs} = independentForestLaw μ₀ j {rs} := by
  rw [taggedFixedForestLaw, Measure.map_apply measurable_inl (measurableSet_singleton _)]
  congr 1
  ext x
  simp

/-- A left-tagged kernel assigns zero mass to every right-tagged atom. -/
theorem tagged_fixed_forest_left_wrong_tag {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) (j : ℕ) (rs : List β) :
    taggedFixedForestLaw μ₀ μ₁ false j {Sum.inr rs} = 0 := by
  rw [taggedFixedForestLaw, Measure.map_apply measurable_inl (measurableSet_singleton _)]
  have hs : (Sum.inl : List α → Sum (List α) (List β)) ⁻¹' {Sum.inr rs} = ∅ := by
    ext x
    simp
  rw [hs, measure_empty]

/-- A right-tagged kernel retains exactly the right independent forest atom. -/
theorem tagged_fixed_forest_right_singleton {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) (j : ℕ) (rs : List β) :
    taggedFixedForestLaw μ₀ μ₁ true j {Sum.inr rs} = independentForestLaw μ₁ j {rs} := by
  rw [taggedFixedForestLaw, Measure.map_apply measurable_inr (measurableSet_singleton _)]
  congr 1
  ext x
  simp

/-- A right-tagged kernel assigns zero mass to every left-tagged atom. -/
theorem tagged_fixed_forest_right_wrong_tag {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) (j : ℕ) (rs : List α) :
    taggedFixedForestLaw μ₀ μ₁ true j {Sum.inl rs} = 0 := by
  rw [taggedFixedForestLaw, Measure.map_apply measurable_inr (measurableSet_singleton _)]
  have hs : (Sum.inr : List β → Sum (List α) (List β)) ⁻¹' {Sum.inl rs} = ∅ := by
    ext x
    simp
  rw [hs, measure_empty]

end SRWTightness
