import SRWTightness.ExternalMarkedGWTree
import SRWTightness.ReferenceMark
import SRWTightness.SourceReferenceIntensity

open MeasureTheory

namespace SRWTightness

/-- The actual reference mark law meets the standard marked-GW input's probability premise. -/
theorem referenceMark_gw_tree_law (D K : Finset Site) (α : ℝ)
    (hinput : MarkedGWTreeInput (Mark K)) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (n : ℕ) :
    finiteRecordReferenceMass (referenceMarkLaw D K α) n Set.univ = 1 ∧
      ∀ s : Set GeometricGWRecord,
        finiteRecordReferenceMass (referenceMarkLaw D K α) n
          {r | finiteRecordPopulationList n r ∈ s} = geometricGWRecordLaw 1 n s := by
  have hμ := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  exact ⟨markedGWTree_mass_one hinput _ hμ n, fun s ↦ hinput _ hμ n s⟩

/-- The source terminal killing domain and intensity give the marked GW reference population law. -/
theorem source_reference_marked_gw_law (b : Site) (m H : ℝ) (K : Finset Site)
    (hinput : MarkedGWTreeInput (Mark K)) (hm : 0 < m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m)
    (hcap : sourceReferenceIntensity m H *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2)
    (n : ℕ) :
    finiteRecordReferenceMass
      (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
        (sourceReferenceIntensity m H)) n Set.univ = 1 ∧
      ∀ s : Set GeometricGWRecord,
        finiteRecordReferenceMass
          (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
            (sourceReferenceIntensity m H)) n {r | finiteRecordPopulationList n r ∈ s} =
              geometricGWRecordLaw 1 n s := by
  exact referenceMark_gw_tree_law _ K _ hinput
    (sourceReferenceIntensity_bounds m H hm hH hHm).1.le (by linarith) n

end SRWTightness
