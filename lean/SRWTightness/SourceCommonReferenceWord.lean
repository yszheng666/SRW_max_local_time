import SRWTightness.ReferenceWordOccupation
import SRWTightness.SourceCommonPairDistanceChernoff

open MeasureTheory
namespace SRWTightness

/-- The actual common reference mark with its entrance and entire ordered killed path. -/
noncomputable def sourceCommonWordLaw (t : ℝ) (b w : Site) (j : ℕ) : Measure WordMark :=
  referenceWordMarkLaw (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w)
    (sourceCommonPairIntensity t j)

/-- The manuscript short-root count on one common ordered reference mark. -/
noncomputable def sourceCommonWordRootCount (t : ℝ) (z : Site) (ν : ℕ) : WordMark → ℕ :=
  wordMarkRootCount
    (sourceEntranceDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν)
    (sourceExitDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν)

/-- The ordered common reference law has exactly the already used occupation projection. -/
theorem source_common_word_occupation (t : ℝ) (b w : Site) (j : ℕ) :
    (sourceCommonWordLaw t b w j).map (wordMarkOccupation (sourceCommonPairObservation b w)) =
      referenceMarkLaw (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w)
        (sourceCommonPairIntensity t j) :=
  referenceWordMarkLaw_occupation _ _ _

end SRWTightness
