import SRWTightness.FiniteKilledWalkMomentInput
import SRWTightness.CountExponentialIntegrable
import SRWTightness.SourceActualNestedRecords
import SRWTightness.SourceCountMeasurable

open MeasureTheory Filter
namespace SRWTightness

/-- The uncapped joint root exponential is integrable under the original walk. Only generic
finite-domain exit moments are supplied externally; the source count comparison is internal. -/
theorem source_root_exponential_integrable (hF : TwoLevelWordFlatteningInput)
    (hExit : FiniteKilledWalkMomentInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      ∀ ν : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      Integrable (fun ω ↦ Real.exp (2 * Real.sqrt (2 * (sourceActualCount t b ν ω : ℝ)) +
        2 * Real.sqrt (2 * (sourceActualCount t w ν ω : ℝ)))) pathLaw := by
  filter_upwards [source_actual_count_direct hF] with t ht
  intro b w hb hw ν hν
  apply joint_count_exponential_integrable pathLaw (sourceActualCount t b ν)
    (sourceActualCount t w ν) (domainSteps (diskFinset (Real.exp t)) 0)
    (measurable_sourceActualCount t b ν) (measurable_sourceActualCount t w ν)
    (hExit (diskFinset (Real.exp t)) 0 8)
  · filter_upwards [ht b hb ν hν] with ω hω
    rw [hω]
    exact killed_child_records_length_le _ _ _ _ _ _
  · filter_upwards [ht w hw ν hν] with ω hω
    rw [hω]
    exact killed_child_records_length_le _ _ _ _ _ _

end SRWTightness
