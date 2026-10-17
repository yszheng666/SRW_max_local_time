import SRWTightness.SourceCommonFarRange
import SRWTightness.SourceCommonEarlyCutoff
import SRWTightness.SourceCommonLevels

open Filter
namespace SRWTightness

/-- Every far pair is either in a valid common level or has the early-range distance cutoff. -/
theorem source_far_pair_split :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (I : ℕ) (b w : Site), 0 < A → b ≠ w →
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) < Real.sqrt (normSq (w - b)) →
      (∃ j ∈ sourceCommonLevels t, j + sourceCommonPairGap t =
        sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))) ∨
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t := by
  obtain ⟨C, hr⟩ := source_common_far_range
  filter_upwards [hr, source_common_early_cutoff, sourceCoarseLowerLevel_eventually_twenty]
    with t hr he hcut
  intro A I b w hA hbw hI hsep
  let ρ := Real.sqrt (normSq (w - b))
  let j := sourceCommonPairLevel t ρ
  by_cases hj : sourceCoarseLowerLevel t ≤ j
  · left
    have hj0 : 0 < j := by omega
    have hi := (sourceCommonPairLevel_eq_iff t ρ j hj0).mp rfl
    have hd := (hr A I j b w hA hbw hI hsep hi).2.2.2
    refine ⟨j, ?_, hi⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj⟩
  · right
    exact he ρ (lt_of_not_ge hj)

end SRWTightness
