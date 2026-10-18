import SRWTightness.ActualFiniteRecordEvent

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The permitted-record sum is exactly the marked reference event mass. -/
theorem finiteRecordReferenceMass_subtype {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (n : ℕ) (s : Set (FiniteExcursionRecord M n)) :
    finiteRecordReferenceMass μ n s =
      ∑' r : s, ENNReal.ofReal (finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r) := by
  classical
  unfold finiteRecordReferenceMass
  simpa only [Set.indicator_apply] using
    (tsum_subtype s
      (fun r ↦ ENNReal.ofReal (finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r))).symm

/-- The population-restricted branching sum is the already defined GW probability. -/
theorem markedGWTree_population_subtype {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (hinput : MarkedGWTreeInput M)
    (μ : Measure M) (hμ : IsProbabilityMeasure μ) (n : ℕ) (s : Set GeometricGWRecord) :
    (∑' r : {r : FiniteExcursionRecord M n | finiteRecordPopulationList n r ∈ s},
      ENNReal.ofReal (finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r)) =
        geometricGWRecordLaw 1 n s := by
  rw [← finiteRecordReferenceMass_subtype]
  exact markedGWTree_population_law hinput μ hμ n s

end SRWTightness
