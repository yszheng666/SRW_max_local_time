import SRWTightness.SourceCommonPairTiltUniform
import SRWTightness.SourceCommonPairLevelRange

open Filter

namespace SRWTightness

/-- Manuscript (9.10): the actual common tilt is admissible, O(1/t), with uniformly bounded cost. -/
theorem source_common_pair_tilt_estimate :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → 1 ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let W := twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
        (sourceCommonPairScaledEndpoint t j) (sourceTerminalHeight t)
      0 < W ∧ (2 / Real.pi) * sourceCommonPairRowScale t b w j * W < 1 ∧
        W ≤ 5 / ((2 / Real.pi) * t) ∧
        (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 * W ^ 2 / 2 ≤ 25 / (2 * (2 / Real.pi)) := by
  filter_upwards [source_common_pair_tilt_uniform, source_common_pair_level_range] with t ht hr
  intro b w j hbw hj hindex hdepth
  have hh := hr j hdepth
  exact ht b w j hbw hj hh.1 hh.2 hindex hdepth

end SRWTightness
