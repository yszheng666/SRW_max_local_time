import SRWTightness.SourceEarlyPrefixExterior
import SRWTightness.ExteriorNestedCountInternal

open Filter
namespace SRWTightness

/-- The original early-prefix exterior measurability statement uses proved count invariance. -/
theorem source_early_prefix_exterior_internal
    (J₀ : ℕ) (hJ₀ : 3 ≤ J₀) :
    ∃ a₀ : ℕ, ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let Z := sourcePairExteriorRecord t b w ν J
      (∃ G : Set ExteriorPathRecord, sourceEarlyPrefixEvent t b j = Z ⁻¹' G) ∧
        @MeasurableSet Sample (MeasurableSpace.comap Z ⊤) (sourceEarlyPrefixEvent t b j) := by
  exact source_early_prefix_exterior exteriorNestedCountInvarianceInput_internal J₀ hJ₀

end SRWTightness
