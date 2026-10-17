import SRWTightness.SourceEarlyDistanceLevels
import SRWTightness.SourceEarlyLongBallDisjoint

open Filter
namespace SRWTightness

/-- Equation 8.8 with its logarithmic gap, positive prefix, continuation range and actual long balls. -/
theorem source_early_distance_geometry (J₀ : ℕ) :
    ∃ a₀ : ℕ, ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      0 < j ∧ (a : ℝ) / 2 ≤ (j : ℝ) ∧ ν ≤ 2 * sourceCoarseLowerLevel t ∧
        (K b ⊆ C b ∧ K w ⊆ C w ∧ C b ∪ C w ⊆ diskFinset (Real.exp t) ∧
          (∀ y ∈ domainExitBoundary (C b), y ∉ C w) ∧
          (∀ y ∈ domainExitBoundary (C w), y ∉ C b) ∧ 0 ∉ C b ∪ C w) ∧
        Disjoint (C b) (C w) := by
  obtain ⟨a₀, hlevels⟩ := source_early_distance_levels J₀
  refine ⟨a₀, ?_⟩
  filter_upwards [hlevels, source_exterior_geometry, source_early_long_balls_disjoint]
    with t ht hg hd
  intro b w hb hw hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let ν := a + J + 5
  have hh := ht a ha hrange
  have ha1 : 1 ≤ a := by have hp := hh.1; omega
  refine ⟨hh.1, hh.2.1, hh.2.2, ?_, ?_⟩
  · exact hg b w ν J hb hw hbw ha1 hh.2.2 rfl
  · exact hd b w ν J hbw ha1 hh.2.2 rfl

end SRWTightness
