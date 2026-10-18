import SRWTightness.SourceLongFineRecord
import SRWTightness.FiniteRecordReferenceMeasure
import SRWTightness.SourceReferenceIntensity

open MeasureTheory
namespace SRWTightness

/-- The probability measure whose atoms occur in the source fine-record comparison. -/
noncomputable def sourceFineReferenceMeasure (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    [MeasurableSpace (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))] :
    Measure (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) :=
  finiteRecordReferenceMeasure
    (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
      (sourceReferenceIntensity (sourceLowerRadius t) 14))
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))

/-- The named source fine mass equals the real atom of its reference measure. -/
theorem sourceFineReferenceMeasure_singleton (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    [MeasurableSpace (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    (r : FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) :
    (sourceFineReferenceMeasure t b K ν).real {r} = sourceLongFineReferenceMass t b K ν r := by
  exact finiteRecordReferenceMeasure_real_singleton _ _ r

/-- The existing standard marked-tree normalization makes the source fine measure a probability. -/
theorem sourceFineReferenceMeasure_probability (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    [MeasurableSpace (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    (hGW : MarkedGWTreeInput (Mark K))
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K ≤ 1) :
    IsProbabilityMeasure (sourceFineReferenceMeasure t b K ν) := by
  exact finiteRecordReferenceMeasure_probability hGW _
    (referenceMarkLaw_isProbabilityMeasure _ _ _ hα hcap) _

end SRWTightness
