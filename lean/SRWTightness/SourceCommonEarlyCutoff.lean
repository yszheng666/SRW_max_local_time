import SRWTightness.SourceCommonLevelIndex
import SRWTightness.SourceSignedDistanceIndex
import SRWTightness.SourceCommonPairCoarseReferenceSum

open Filter
namespace SRWTightness

/-- Equation (9.16): a common level below the coarse cutoff has the required early distance index. -/
theorem source_common_early_cutoff :
    ∀ᶠ t : ℝ in atTop, ∀ ρ : ℝ,
      sourceCommonPairLevel t ρ < sourceCoarseLowerLevel t →
      sourceCommonPairDistanceIndex t ρ < sourceCoarseLowerLevel t + sourceCommonPairGap t := by
  filter_upwards [sourceCoarseLowerLevel_eventually_twenty] with t ht
  intro ρ hlevel
  unfold sourceCommonPairLevel at hlevel
  omega

/-- The signed version of (9.16) does not require a nonnegative common index. -/
theorem source_common_signed_early_cutoff (t ρ : ℝ)
    (h : sourceSignedDistanceIndex t ρ - (sourceCommonPairGap t : ℤ) <
      (sourceCoarseLowerLevel t : ℤ)) :
    sourceSignedDistanceIndex t ρ < ((sourceCoarseLowerLevel t + sourceCommonPairGap t : ℕ) : ℤ) := by
  omega

end SRWTightness
