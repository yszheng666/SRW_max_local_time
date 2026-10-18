import SRWTightness.IndependentForestMap
import SRWTightness.GeometricGWLaw

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

local instance independentForestSumNatListMeasurable :
    MeasurableSpace (List ℕ) := inferInstanceAs (MeasurableSpace GeometricGWRecord)
local instance independentForestSumNatListSingleton :
    MeasurableSingletonClass (List ℕ) :=
  inferInstanceAs (MeasurableSingletonClass GeometricGWRecord)

/-- The sum of an ordered independent natural-valued forest has the corresponding product law. -/
theorem independent_forest_sum_law (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    (independentForestLaw μ k).map List.sum =
      (Measure.pi (fun _ : Fin k ↦ μ)).map (fun ξ ↦ ∑ i, ξ i) := by
  rw [independentForestLaw, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  congr 1
  funext ξ
  exact List.sum_ofFn

/-- Summing an independent forest of critical geometric counts gives the existing GW generation. -/
theorem independent_geometric_forest_generation (k : ℕ) :
    (independentForestLaw geometricGWOffspringLaw k).map List.sum =
      geometricGWGenerationLaw k := by
  exact independent_forest_sum_law geometricGWOffspringLaw k

end SRWTightness
