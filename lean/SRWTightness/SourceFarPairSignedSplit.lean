import SRWTightness.SourceFarPairSplit
import SRWTightness.SourceCommonSignedLevel

open Filter

namespace SRWTightness

/-- The far-pair partition uses the literal signed floor and the literal signed common level. -/
theorem source_far_pair_signed_split :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (I : ℕ) (b w : Site), 0 < A → b ≠ w →
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) < Real.sqrt (normSq (w - b)) →
      (∃ j ∈ sourceCommonLevels t, (j : ℤ) =
        sourceSignedCommonPairLevel t (Real.sqrt (normSq (w - b)))) ∨
      sourceSignedDistanceIndex t (Real.sqrt (normSq (w - b))) <
        ((sourceCoarseLowerLevel t + sourceCommonPairGap t : ℕ) : ℤ) := by
  filter_upwards [source_far_pair_split, sourceCoarseLowerLevel_eventually_twenty,
    eventually_ge_atTop (1 : ℝ)] with t hs hc ht
  intro A I b w hA hbw hI hsep
  rcases hs A I b w hA hbw hI hsep with ⟨j, hj, he⟩ | he
  · left
    have hl := (Finset.mem_filter.mp hj).2
    have hp : 0 < sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) := by omega
    have hz := source_signed_distance_eq_natural t (Real.sqrt (normSq (w - b))) hp
    refine ⟨j, hj, ?_⟩
    unfold sourceSignedCommonPairLevel
    rw [hz]
    have hg := source_common_pair_gap_integer t ht
    omega
  · right
    exact (source_signed_distance_le_natural t (Real.sqrt (normSq (w - b)))).trans_lt
      (Int.ofNat_lt.mpr he)

end SRWTightness
