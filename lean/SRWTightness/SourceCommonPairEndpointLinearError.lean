import SRWTightness.SourceCommonPairEndpointError
import SRWTightness.SourceCommonPairRadiusLower

namespace SRWTightness

/-- On permitted positive endpoints, the barrier endpoint is at most linear in source time. -/
theorem source_common_pair_endpoint_linear (t : ℝ) (j : ℕ)
    (ht : sourceScaleThreshold 4 ≤ t) (htE : 2 * sourceTotalTimeError ≤ t)
    (hjt : (j : ℝ) ≤ t) (hjT : (j : ℝ) ≤ sourceTotalTime t)
    (hq : 0 ≤ sourceCommonPairEndpoint t j) :
    |sourceCommonPairEndpoint t j| ≤ 4 + 4 * t := by
  have hs := (sourceBarrierSlope_bounds t ht htE).2
  have hp : 0 ≤ (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) :=
    Real.rpow_nonneg (le_min (Nat.cast_nonneg _) (sub_nonneg.mpr hjT)) _
  have hm := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  rw [abs_of_nonneg hq]
  unfold sourceCommonPairEndpoint
  linarith

/-- A single terminal-radius error bound controls every allowed positive coarse endpoint. -/
theorem source_common_pair_endpoint_linear_error (t : ℝ) (j : ℕ)
    (ht : sourceScaleThreshold 4 ≤ t) (htE : 2 * sourceTotalTimeError ≤ t)
    (hjt : (j : ℝ) ≤ t) (hjT : (j : ℝ) ≤ sourceTotalTime t)
    (hq : 0 ≤ sourceCommonPairEndpoint t j)
    (hdepth : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) :
    |sourceCommonPairScaledEndpoint t j - sourceCommonPairEndpoint t j| ≤
      56 * (4 + 4 * t) / sourceLowerRadius t := by
  have hlo := sourceCommonPairInnerRadius_ge_lower t j hdepth
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  have he := source_common_pair_endpoint_error t j (hm70.trans hlo)
  have hqbound := source_common_pair_endpoint_linear t j ht htE hjt hjT hq
  calc
    _ ≤ 56 * |sourceCommonPairEndpoint t j| / sourceCommonPairInnerRadius t j := he
    _ ≤ 56 * |sourceCommonPairEndpoint t j| / sourceLowerRadius t :=
      div_le_div_of_nonneg_left (by positivity) (sourceLowerRadius_pos t) hlo
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqbound (by norm_num))
      (sourceLowerRadius_pos t).le

end SRWTightness
