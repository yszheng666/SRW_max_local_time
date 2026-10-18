import SRWTightness.CountableProbabilityBindProduct
import SRWTightness.GeometricMarkedListBind
import SRWTightness.IndependentForestAppend
import SRWTightness.MeasureBindMap

open MeasureTheory

namespace SRWTightness

/-- Appending one geometric child forest to an independent count-mixture adds their exact counts. -/
theorem geometric_forest_bind_convolution {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ]
    (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    ((geometricMarkedListLaw μ).prod (ν.bind (independentForestLaw μ))).map
      (fun q ↦ q.1 ++ q.2) =
      (geometricGWOffspringLaw.prod ν).bind
        (fun q ↦ independentForestLaw μ (q.1 + q.2)) := by
  rw [geometric_marked_list_bind, countable_probability_bind_product,
    measure_bind_map_output _ _ _ (measurable_of_countable _) (measurable_of_countable _)]
  apply congrArg ((geometricGWOffspringLaw.prod ν).bind)
  funext q
  exact independent_forest_append_law μ q.1 q.2

end SRWTightness
