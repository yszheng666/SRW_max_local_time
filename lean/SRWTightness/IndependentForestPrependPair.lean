import SRWTightness.IndependentForestAppend

open MeasureTheory

namespace SRWTightness

/-- Prepending an independent left forest preserves the independent right forest exactly. -/
theorem independent_forest_prepend_left {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (j k l : ℕ) :
    ((independentForestLaw μ₀ j).prod
      ((independentForestLaw μ₀ k).prod (independentForestLaw μ₁ l))).map
        (fun q ↦ (q.1 ++ q.2.1, q.2.2)) =
      (independentForestLaw μ₀ (j + k)).prod (independentForestLaw μ₁ l) := by
  have ha : MeasurePreserving (fun q : List α × List α ↦ q.1 ++ q.2)
      ((independentForestLaw μ₀ j).prod (independentForestLaw μ₀ k))
      (independentForestLaw μ₀ (j + k)) :=
    ⟨measurable_of_countable _, independent_forest_append_law μ₀ j k⟩
  have hs := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (independentForestLaw μ₀ j)
      (independentForestLaw μ₀ k) (independentForestLaw μ₁ l))
  exact ((ha.prod (MeasurePreserving.id (independentForestLaw μ₁ l))).comp hs).map_eq

/-- Prepending an independent right forest preserves the independent left forest exactly. -/
theorem independent_forest_prepend_right {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    (μ₀ : Measure α) (μ₁ : Measure β) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (j k l : ℕ) :
    ((independentForestLaw μ₁ j).prod
      ((independentForestLaw μ₀ k).prod (independentForestLaw μ₁ l))).map
        (fun q ↦ (q.2.1, q.1 ++ q.2.2)) =
      (independentForestLaw μ₀ k).prod (independentForestLaw μ₁ (j + l)) := by
  have ha : MeasurePreserving (fun q : List β × List β ↦ q.1 ++ q.2)
      ((independentForestLaw μ₁ j).prod (independentForestLaw μ₁ l))
      (independentForestLaw μ₁ (j + l)) :=
    ⟨measurable_of_countable _, independent_forest_append_law μ₁ j l⟩
  have h₀ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (independentForestLaw μ₁ j)
      (independentForestLaw μ₀ k) (independentForestLaw μ₁ l))
  have h₁ := (Measure.measurePreserving_swap (μ := independentForestLaw μ₁ j)
    (ν := independentForestLaw μ₀ k)).prod
      (MeasurePreserving.id (independentForestLaw μ₁ l))
  have h₂ := measurePreserving_prodAssoc (independentForestLaw μ₀ k)
    (independentForestLaw μ₁ j) (independentForestLaw μ₁ l)
  have h₃ := (MeasurePreserving.id (independentForestLaw μ₀ k)).prod ha
  exact (h₃.comp (h₂.comp (h₁.comp h₀))).map_eq

end SRWTightness
