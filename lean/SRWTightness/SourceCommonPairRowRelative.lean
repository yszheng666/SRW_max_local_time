import SRWTightness.SourceCommonPairRowEstimate
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceCommonPairLogTime

open Filter

namespace SRWTightness

/-- The common row-scale error is eventually at most a tenth of the remaining source time. -/
theorem source_common_pair_row_relative_upper :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      sourceCommonPairRowScale t b w j ≤ (11 / 10 : ℝ) * (sourceTotalTime t - (j : ℝ)) := by
  obtain ⟨C, hC, hrow⟩ := source_common_pair_row_estimate
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [hrow, eventually_ge_atTop T, eventually_ge_atTop (sourceScaleThreshold 4),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (C + 2 * |sourceTotalTimeError| + 100)))] with t hr ht hs hl
  intro b w j hbw hj hdepth
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans hl
  have hlogC : C + 2 * |sourceTotalTimeError| + 100 ≤ Real.log t := (le_max_right _ _).trans hl
  have hm := sourceLowerRadius_pos t
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    have hh := (hT t ht).2
    nlinarith [Real.exp_one_gt_two]
  have hi := (source_common_pair_inner_log_time t j hscale).2
  have hmi := Real.log_le_log hm (sourceCommonPairInnerRadius_ge_lower t j hdepth)
  have hgrowth : 2000 * Real.log t ≤ Real.log (sourceLowerRadius t) := by
    rw [log_sourceLowerRadius]
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ 2000 * Real.log t) (by norm_num : (1 : ℝ) ≤ 5 / 2)
    simpa only [Real.rpow_one, sourceLowerLogRadius] using hp
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) hs).1
  have hJ := (sourceCommonPairGap_bounds t (by linarith)).2
  have hD := (abs_le.mp (hr b w j hbw hj hdepth)).2
  have htime := (abs_le.mp (sourceTotalTime_error t hs)).1
  have hc : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hE := le_abs_self sourceTotalTimeError
  have hE0 := abs_nonneg sourceTotalTimeError
  linarith

end SRWTightness
