import SRWTightness.IndependentForestAppend
import SRWTightness.IndependentForestSingleton

open MeasureTheory

namespace SRWTightness

/-- Adding one independently marked first root gives the exact successor-size ordered forest. -/
theorem independent_forest_cons_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] (k : ℕ) :
    independentForestLaw μ (k + 1) =
      (μ.prod (independentForestLaw μ k)).map (fun q ↦ q.1 :: q.2) := by
  rw [show k + 1 = 1 + k by omega, ← independent_forest_append_law,
    independent_forest_singleton_law]
  have hm : (μ.map (fun x ↦ [x])).prod (independentForestLaw μ k) =
      (μ.prod (independentForestLaw μ k)).map (fun q ↦ ([q.1], q.2)) := by
    simpa only [Measure.map_id, Prod.map_def, id_eq] using
      Measure.map_prod_map μ (independentForestLaw μ k)
        (measurable_of_countable (fun x : M ↦ [x])) measurable_id
  rw [hm, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

end SRWTightness
