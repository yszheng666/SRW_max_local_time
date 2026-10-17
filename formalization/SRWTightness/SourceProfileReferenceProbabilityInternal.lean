import SRWTightness.SourceProfileReferenceMeasure
import SRWTightness.MarkedTreeNormalization

open MeasureTheory
namespace SRWTightness

/-- Actual source reference trees are probability measures without an assumed marked-tree law. -/
theorem source_profile_reference_probability_internal (b : Site) (t a : ℝ) (K : Finset Site)
    (ht : sourceCapacityHalfThreshold ≤ t) (ha : 1 ≤ a)
    (hcut : a ≤ sourceLowerRadius t / t ^ 6) (hK : K ⊆ translateFinset b (diskFinset a))
    (n : ℕ) [MeasurableSpace (FiniteExcursionRecord (Mark K) n)]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) n)] :
    IsProbabilityMeasure (finiteRecordReferenceMeasure
      (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
        (sourceReferenceIntensity (sourceLowerRadius t) 14)) n) := by
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_left _ _).trans ht
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1.le
  have hcap := source_capacity_half_profile b t a K ht ha hcut hK
  letI := referenceMarkLaw_isProbabilityMeasure _ K
    (sourceReferenceIntensity (sourceLowerRadius t) 14) hα (by linarith)
  exact finite_record_reference_measure_probability_internal _ n

end SRWTightness
