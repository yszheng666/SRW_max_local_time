import SRWTightness.SourceCommonPairEndpointError

namespace SRWTightness

/-- The source intensity normalization can only raise a nonnegative endpoint. -/
theorem sourceCommonPairScaledEndpoint_ge (t : ℝ) (j : ℕ)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) (hq : 0 ≤ sourceCommonPairEndpoint t j) :
    sourceCommonPairEndpoint t j ≤ sourceCommonPairScaledEndpoint t j := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have he := (sourceReferenceIntensity_error (sourceCommonPairInnerRadius t j) 14
    (sourceCommonPairInnerRadius_pos t j) (by norm_num) (by linarith)).1
  have hr : 1 ≤ sourceCommonPairIntensity t j / (2 / Real.pi) :=
    (one_le_div hg).mpr (by exact le_of_sub_nonneg he)
  have hs : 1 ≤ Real.sqrt (sourceCommonPairIntensity t j / (2 / Real.pi)) := by
    simpa using Real.sqrt_le_sqrt hr
  unfold sourceCommonPairScaledEndpoint
  nlinarith

/-- The actual normalized endpoint deficit is at most five times the remaining source time. -/
theorem source_common_pair_endpoint_deficit (t : ℝ) (j : ℕ)
    (ht : sourceScaleThreshold 4 ≤ t) (htE : 2 * sourceTotalTimeError ≤ t)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) (hq : 0 ≤ sourceCommonPairEndpoint t j)
    (hd : 1 ≤ sourceTotalTime t - (j : ℝ)) :
    sourceTerminalHeight t - sourceCommonPairScaledEndpoint t j ≤
      5 * (sourceTotalTime t - (j : ℝ)) := by
  have hB := sourceCommonPairScaledEndpoint_ge t j hm hq
  have hs := (sourceBarrierSlope_bounds t ht htE).2
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hT := sourceTotalTime_ge_half t ht htE
  have hT0 : sourceTotalTime t ≠ 0 := by linarith
  have he : sourceBarrierSlope t * sourceTotalTime t = sourceTerminalHeight t :=
    div_mul_cancel₀ _ hT0
  have hp := Real.rpow_le_rpow
    (le_min (Nat.cast_nonneg j : (0 : ℝ) ≤ j) (by linarith : 0 ≤ sourceTotalTime t - j))
    (min_le_right (j : ℝ) (sourceTotalTime t - j)) (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hp' := Real.rpow_le_rpow_of_exponent_le hd (by norm_num : (2 / 5 : ℝ) ≤ 1)
  rw [Real.rpow_one] at hp'
  have hmθ := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ sourceTotalTime t - j)
  unfold sourceCommonPairEndpoint at hB
  nlinarith

end SRWTightness
