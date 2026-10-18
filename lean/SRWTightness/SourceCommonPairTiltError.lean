import SRWTightness.SourceCommonPairEndpointDeficit
import SRWTightness.TwoSiteOptimizedErrorBound

namespace SRWTightness

/-- The source endpoint deficit bounds the common tilt by O(1/t) and its quadratic cost by a constant. -/
theorem source_common_pair_tilt_error (t : ℝ) (b w : Site) (j : ℕ)
    (ht : sourceScaleThreshold 4 ≤ t) (htE : 2 * sourceTotalTimeError ≤ t)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) (hq : 0 < sourceCommonPairEndpoint t j)
    (hd : 1 ≤ sourceTotalTime t - (j : ℝ))
    (hD : sourceTotalTime t - (j : ℝ) ≤ sourceCommonPairRowScale t b w j)
    (hBy : sourceCommonPairScaledEndpoint t j < sourceTerminalHeight t) :
    let W := twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
      (sourceCommonPairScaledEndpoint t j) (sourceTerminalHeight t)
    W ≤ 5 / ((2 / Real.pi) * t) ∧
      (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 * W ^ 2 / 2 ≤ 25 / (2 * (2 / Real.pi)) := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hy : t ≤ sourceTerminalHeight t := by
    unfold sourceTerminalHeight
    linarith [Real.log_le_sub_one_of_pos ht0]
  have hgap := source_common_pair_endpoint_deficit t j ht htE hm hq.le hd
  have hh := twoSiteOptimizedTilt_error_bound (2 / Real.pi) (sourceCommonPairRowScale t b w j)
    (sourceCommonPairScaledEndpoint t j) (sourceTerminalHeight t) 5 hg (by linarith)
    (sourceCommonPairScaledEndpoint_pos t j hm hq) hBy (by norm_num) (by linarith)
  constructor
  · exact hh.1.trans (div_le_div_of_nonneg_left (by norm_num) (mul_pos hg ht0)
      (mul_le_mul_of_nonneg_left hy hg.le))
  · simpa only [show (5 : ℝ) ^ 2 = 25 by norm_num] using hh.2

end SRWTightness
