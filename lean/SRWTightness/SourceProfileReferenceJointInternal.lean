import SRWTightness.MarkedGWInputsInternal
import SRWTightness.ExternalMarkedGWJoint
import SRWTightness.SourceProfileReferenceMeasure

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual source cutoff and intensity validate the terminal independent-mark joint interface. -/
theorem source_profile_reference_joint_internal (b : Site) (t a : ℝ) (K : Finset Site)
    [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))]
    (ht : sourceCapacityHalfThreshold ≤ t)
    (ha : 1 ≤ a) (hcut : a ≤ sourceLowerRadius t / t ^ 6)
    (hK : K ⊆ translateFinset b (diskFinset a)) (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord (Mark K) n)]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) n)]
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List (Mark K))) :
    let μ := referenceMarkLaw
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
      (sourceReferenceIntensity (sourceLowerRadius t) 14)
    finiteRecordReferenceMeasure μ n {r | finiteRecordPopulationList n r ∈ s ∧
      finiteRecordLeaves n r ∈ E (finiteRecordPopulationList n r)} =
        ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g n) (E g)
          ∂geometricGWRecordLaw 1 n := by
  dsimp only
  rw [finiteRecordReferenceMeasure_apply]
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_left _ _).trans ht
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1.le
  have hcap := source_capacity_half_profile b t a K ht ha hcut hK
  exact marked_gw_joint_input_internal _
    (referenceMarkLaw_isProbabilityMeasure _ _ _ hα (by linarith)) n s E

end SRWTightness
