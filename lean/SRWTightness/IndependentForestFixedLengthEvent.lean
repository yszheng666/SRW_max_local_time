import SRWTightness.GeometricMarkedListJoint

open MeasureTheory

namespace SRWTightness

/-- An arbitrary length-dependent forest event uses its actual deterministic root count. -/
theorem independent_forest_fixed_length_event {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) [IsProbabilityMeasure μ]
    (k : ℕ) (E : ℕ → Set (List M)) :
    independentForestLaw μ k {rs | rs ∈ E rs.length} = independentForestLaw μ k (E k) := by
  simpa only [Set.mem_univ, true_and, if_true] using
    independent_forest_length_event μ k Set.univ E

end SRWTightness
