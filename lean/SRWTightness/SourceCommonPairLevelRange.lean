import SRWTightness.SourceCommonPairLogTime
import SRWTightness.SourceCommonPairRadiusLower
import SRWTightness.SourceForestApplicationGeometry

open Filter

namespace SRWTightness

/-- The actual root-depth range eventually implies both time conditions used in tilt optimization. -/
theorem source_common_pair_level_range :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ,
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      (j : ℝ) ≤ t ∧ 6 ≤ sourceTotalTime t - (j : ℝ) := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (sourceScaleThreshold 4),
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (sourceTotalTimeError + 6)))] with t ht hs hl
  intro j hdepth
  have hm := sourceLowerRadius_pos t
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    have hh := (hT t ht).2
    nlinarith [Real.exp_one_gt_two]
  have hi := (source_common_pair_inner_log_time t j hscale).2
  have hmi := Real.log_le_log hm (sourceCommonPairInnerRadius_ge_lower t j hdepth)
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans hl
  have hlogE : sourceTotalTimeError + 6 ≤ Real.log t := (le_max_right _ _).trans hl
  have hgrowth := sourceLowerLogRadius_ge_seven_log t hlog1
  rw [← log_sourceLowerRadius] at hgrowth
  have htime := (abs_le.mp (sourceTotalTime_error t hs)).1
  have hc : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  constructor <;> linarith

end SRWTightness
