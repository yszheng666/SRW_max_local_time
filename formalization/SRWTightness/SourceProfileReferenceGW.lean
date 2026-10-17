import SRWTightness.SourceCapacityHalfProfile
import SRWTightness.ReferenceMarkGWTree

namespace SRWTightness

/-- The actual source cutoff discharges the capacity premise of the marked GW reference law. -/
theorem source_profile_reference_gw (b : Site) (t a : ℝ) (K : Finset Site)
    (hinput : MarkedGWTreeInput (Mark K)) (ht : sourceCapacityHalfThreshold ≤ t)
    (ha : 1 ≤ a) (hcut : a ≤ sourceLowerRadius t / t ^ 6)
    (hK : K ⊆ translateFinset b (diskFinset a)) (n : ℕ) :
    finiteRecordReferenceMass
      (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
        (sourceReferenceIntensity (sourceLowerRadius t) 14)) n Set.univ = 1 ∧
      ∀ s : Set GeometricGWRecord,
        finiteRecordReferenceMass
          (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
            (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
            {r | finiteRecordPopulationList n r ∈ s} = geometricGWRecordLaw 1 n s := by
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_left _ _).trans ht
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).2.2.1
  exact source_reference_marked_gw_law b _ 14 K hinput (sourceLowerRadius_pos t)
    (by norm_num) (by linarith) (source_capacity_half_profile b t a K ht ha hcut hK) n

end SRWTightness
