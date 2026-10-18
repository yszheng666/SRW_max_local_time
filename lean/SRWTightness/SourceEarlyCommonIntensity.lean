import SRWTightness.SourceEarlyLevelBounds
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceReferenceIntensityError

open Filter
namespace SRWTightness

/-- Equation 8.13 uniformly at every early common level, with the actual buffered source radii
and an explicit inverse-radius error. No time-gap specialization is used. -/
theorem source_early_common_intensity :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ 2 * sourceCoarseLowerLevel t →
      sourceCommonPairIntensity t j = (2 / Real.pi) * Real.log
        ((sourceRecordRadius (sourceLowerRadius t)
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) j + 14) /
            (sourceCommonPairInnerRadius t j - 14)) ∧
      0 < sourceCommonPairIntensity t j ∧
      sourceCommonPairIntensity t j ≤ 2 * (2 / Real.pi) ∧
      |sourceCommonPairIntensity t j - (2 / Real.pi)| ≤
        56 * (2 / Real.pi) / sourceCommonPairInnerRadius t j := by
  filter_upwards [source_early_level_bounds,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (70 : ℝ))]
    with t ht hm
  intro j hj
  have hr := hm.trans (sourceCommonPairInnerRadius_ge_lower t j (ht.2 j hj).1)
  exact ⟨sourceCommonPairIntensity_eq t j, (sourceCommonPairIntensity_bounds t j hr).1,
    (sourceCommonPairIntensity_bounds t j hr).2,
    sourceReferenceIntensity_fourteen_error _ hr⟩

end SRWTightness
