import SRWTightness.SourceCommonPairEndpointRatio
import SRWTightness.SourceCommonPairEndpointInterval
import SRWTightness.SourceCommonPairLevelRange
import SRWTightness.SourceCommonPairRowRelative
import SRWTightness.SourceCommonPairRowLower
import SRWTightness.TwoSiteGWRelativeCoefficient

open Filter

namespace SRWTightness

/-- The actual common-endpoint exponent has a positive GW-weighted quadratic coefficient. -/
theorem source_common_pair_gw_coefficient_pos :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → 20 ≤ j →
      20 ≤ sourceTotalTime t - (j : ℝ) →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let W := twoSiteOptimizedTilt (2 / Real.pi) (sourceCommonPairRowScale t b w j)
        (sourceCommonPairScaledEndpoint t j) (sourceTerminalHeight t)
      0 < sourceCommonPairIntensity t j * W /
        (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j * W) - 1 / (2 * ((j : ℝ) + 1)) := by
  filter_upwards [sourceBarrierSlope_eventually_band, source_common_pair_endpoint_interval,
    source_common_pair_endpoint_error_uniform 1 (by norm_num), source_common_pair_level_range,
    source_common_pair_row_relative_upper, source_common_pair_row_ge_remaining,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hθ hi he hl hru hrl ht
  intro b w j hbw hj hd hindex hdepth
  have htime := hl j hdepth
  have hv := hi j (by omega) htime.1 (by linarith) hdepth
  have herr := (he j htime.1 (by linarith) hv.1.le hdepth).le
  have hrat := source_common_pair_endpoint_ratios t j hθ hj hd herr
  have hDu := hru b w j hbw hindex hdepth
  have hDl := hrl b w j hbw hindex hdepth
  have hm := ((sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1).trans
    (sourceCommonPairInnerRadius_ge_lower t j hdepth)
  have hα := (sourceReferenceIntensity_error (sourceCommonPairInnerRadius t j) 14
    (sourceCommonPairInnerRadius_pos t j) (by norm_num) (by linarith)).1
  exact twoSiteOptimizedTilt_gw_coefficient_of_ratios (2 / Real.pi) (sourceCommonPairRowScale t b w j)
    (sourceCommonPairScaledEndpoint t j) (sourceTerminalHeight t) (sourceCommonPairIntensity t j)
    j (sourceTotalTime t - j) (by positivity) (by linarith) hv.2.1
    (lt_trans hv.2.1 hv.2.2) (Nat.cast_nonneg j) (by linarith)
    (le_of_sub_nonneg hα) hDu hrat.1 hrat.2

end SRWTightness
