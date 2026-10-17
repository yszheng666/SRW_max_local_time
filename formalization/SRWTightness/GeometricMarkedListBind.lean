import SRWTightness.CountableMeasureBindSum
import SRWTightness.GeometricMarkedListLaw

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- The constructed ordered marked branching law is its exact geometric-count kernel mixture. -/
theorem geometric_marked_list_bind {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ] :
    geometricMarkedListLaw μ = geometricGWOffspringLaw.bind (independentForestLaw μ) := by
  exact (countable_measure_bind_sum geometricGWOffspringLaw (independentForestLaw μ)).symm

/-- A generation with zero parents has exactly zero offspring. -/
theorem geometric_gw_generation_zero : geometricGWGenerationLaw 0 = Measure.dirac 0 := by
  unfold geometricGWGenerationLaw
  have hf : (fun ξ : Fin 0 → ℕ ↦ ∑ i, ξ i) = fun _ ↦ 0 := by
    funext ξ
    simp
  rw [hf, Measure.map_const, measure_univ, one_smul]

end SRWTightness
