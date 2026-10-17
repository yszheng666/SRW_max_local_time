import SRWTightness.SourceCommonPairEndpointInterval
import SRWTightness.SourceCommonPairRowLower
import SRWTightness.SourceCommonPairTiltError

open Filter

namespace SRWTightness

/-- All optimized-tilt conditions and errors hold uniformly on the actual common coarse range. -/
theorem source_common_pair_tilt_uniform :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → 1 ≤ j → (j : ℝ) ≤ t →
      6 ≤ sourceTotalTime t - (j : ℝ) →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let W := twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
        (sourceCommonPairScaledEndpoint t j) (sourceTerminalHeight t)
      0 < W ∧ (2 / Real.pi) * sourceCommonPairRowScale t b w j * W < 1 ∧
        W ≤ 5 / ((2 / Real.pi) * t) ∧
        (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 * W ^ 2 / 2 ≤ 25 / (2 * (2 / Real.pi)) := by
  filter_upwards [source_common_pair_endpoint_interval, source_common_pair_row_ge_remaining,
    eventually_ge_atTop (sourceScaleThreshold 4),
    eventually_ge_atTop (2 * sourceTotalTimeError)] with t hi hr ht htE
  intro b w j hbw hj hjt hd hindex hdepth
  have he := hi j hj hjt hd hdepth
  have hD := hr b w j hbw hindex hdepth
  have hm := ((sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1).trans
    (sourceCommonPairInnerRadius_ge_lower t j hdepth)
  have ha := twoSiteOptimizedTilt_admissible (2 / Real.pi) (sourceCommonPairRowScale t b w j)
    (sourceCommonPairScaledEndpoint t j) (sourceTerminalHeight t) (by positivity)
    (by linarith) he.2.1 he.2.2
  have hb := source_common_pair_tilt_error t b w j ht htE hm he.1 (by linarith) hD he.2.2
  exact ⟨ha.1, ha.2, hb.1, hb.2⟩

end SRWTightness
