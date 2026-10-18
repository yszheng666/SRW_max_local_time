import SRWTightness.SourceGroupedFineError

open MeasureTheory Filter
namespace SRWTightness

/-- Marking each short root leaves the original root count unchanged after long-segment grouping. -/
theorem source_grouped_fine_count (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ z : Site, z = b ∨ z = w → ∀ Kobs : Finset Site,
      ∀ᵐ ω ∂pathLaw,
        (sourceGroupedFineForest t b w z Kobs ν J ω).length = sourceActualCount t z ν ω := by
  filter_upwards [source_long_grouped_records hF] with t ht
  intro b w ν J hb hw hbw ha hν hform z hz Kobs
  filter_upwards [ht b w ν J hb hw hbw ha hν hform z hz
    (sourceLongFineRecord t z Kobs ν)] with ω hω
  simpa only [sourceGroupedFineForest, List.length_map, sourceActualCount,
    sourceForwardRecordCount, Nat.sub_zero] using (congrArg List.length hω).symm

end SRWTightness
