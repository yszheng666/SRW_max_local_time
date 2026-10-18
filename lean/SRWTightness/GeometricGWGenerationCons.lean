import SRWTightness.IndependentForestCons
import SRWTightness.IndependentForestSum

open MeasureTheory

namespace SRWTightness

attribute [local instance] independentForestSumNatListMeasurable
  independentForestSumNatListSingleton

/-- The actual GW generation with one more parent is the sum of one independent geometric count. -/
theorem geometric_gw_generation_cons (k : ℕ) :
    geometricGWGenerationLaw (k + 1) =
      (geometricGWOffspringLaw.prod (geometricGWGenerationLaw k)).map
        (fun q ↦ q.1 + q.2) := by
  rw [← independent_geometric_forest_generation, independent_forest_cons_law,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have hm : geometricGWOffspringLaw.prod (geometricGWGenerationLaw k) =
      (geometricGWOffspringLaw.prod (independentForestLaw geometricGWOffspringLaw k)).map
        (fun q ↦ (q.1, q.2.sum)) := by
    rw [← independent_geometric_forest_generation]
    simpa only [Measure.map_id, Prod.map_def, id_eq] using
      Measure.map_prod_map geometricGWOffspringLaw
        (independentForestLaw geometricGWOffspringLaw k) measurable_id
        (measurable_of_countable List.sum)
  rw [hm, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

end SRWTightness
