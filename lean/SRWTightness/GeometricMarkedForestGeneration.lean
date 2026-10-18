import SRWTightness.IndependentForestSum
import SRWTightness.GeometricMarkedListJoint

open MeasureTheory

namespace SRWTightness

attribute [local instance] independentForestSumNatListMeasurable
  independentForestSumNatListSingleton

/-- The total child count of independent marked roots is the actual critical GW generation law. -/
theorem geometric_marked_forest_generation_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] [MeasurableSpace (List (List M))]
    [MeasurableSingletonClass (List (List M))]
    (μ : Measure M) [IsProbabilityMeasure μ] (k : ℕ) :
    (independentForestLaw (geometricMarkedListLaw μ) k).map
      (fun rs ↦ (rs.map List.length).sum) = geometricGWGenerationLaw k := by
  have hf : (fun rs : List (List M) ↦ (rs.map List.length).sum) =
      List.sum ∘ List.map List.length := rfl
  rw [hf, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    independent_forest_map, geometric_marked_list_length_law]
  exact independent_geometric_forest_generation k

end SRWTightness
