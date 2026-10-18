import SRWTightness.FiniteRecordReferenceMeasure
import SRWTightness.SourceProfileReferenceGW

open MeasureTheory

namespace SRWTightness

/-- The actual source-profile tree measure is normalized and has the existing GW population law. -/
theorem source_profile_reference_measure (b : Site) (t a : ℝ) (K : Finset Site)
    (hinput : MarkedGWTreeInput (Mark K)) (ht : sourceCapacityHalfThreshold ≤ t)
    (ha : 1 ≤ a) (hcut : a ≤ sourceLowerRadius t / t ^ 6)
    (hK : K ⊆ translateFinset b (diskFinset a)) (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord (Mark K) n)]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) n)] :
    let μ := referenceMarkLaw
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
      (sourceReferenceIntensity (sourceLowerRadius t) 14)
    IsProbabilityMeasure (finiteRecordReferenceMeasure μ n) ∧
      ∀ s : Set GeometricGWRecord,
        finiteRecordReferenceMeasure μ n {r | finiteRecordPopulationList n r ∈ s} =
          geometricGWRecordLaw 1 n s := by
  dsimp only
  have hh := source_profile_reference_gw b t a K hinput ht ha hcut hK n
  constructor
  · constructor
    rw [finiteRecordReferenceMeasure_apply]
    exact hh.1
  · intro s
    rw [finiteRecordReferenceMeasure_apply]
    exact hh.2 s

end SRWTightness
