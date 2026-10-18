import SRWTightness.SourceTiltIntensityBound
import SRWTightness.SourceLowerTimeSmallError

open Filter
open scoped Topology

namespace SRWTightness

noncomputable def sourceGreenScaleSlope : ℝ :=
  (2 / Real.pi) + diskGreenEnergyConstant +
    (2 / Real.pi) * (sourceLowerTimeError + Real.log 4 + Real.log 2)

theorem sourceGreenScaleSlope_pos : 0 < sourceGreenScaleSlope := by
  have hE := sourceLowerTimeError_pos
  have hB := diskGreenEnergyConstant_pos
  have h4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  unfold sourceGreenScaleSlope
  positivity

/-- The explicit uniform Green scale is at most a fixed multiple of the actual source time. -/
theorem sourceUniformGreenScale_le_time (m : ℝ) (hd : 1 ≤ sourceLowerTime m) :
    sourceUniformGreenScale m ≤ sourceGreenScaleSlope * sourceLowerTime m := by
  have hC : 0 ≤ diskGreenEnergyConstant +
      (2 / Real.pi) * (sourceLowerTimeError + Real.log 4 + Real.log 2) := by
    have hE := sourceLowerTimeError_pos
    have hB := diskGreenEnergyConstant_pos
    have h4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hh := mul_le_mul_of_nonneg_left hd hC
  unfold sourceUniformGreenScale sourceGreenScaleSlope
  nlinarith

/-- The same explicit source threshold makes the Green-function time at least one. -/
theorem sourceLowerTime_ge_one (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t) :
    1 ≤ sourceLowerTime (sourceLowerRadius t) := by
  obtain ⟨_, _, hm, hl⟩ := sourceScaleThreshold_conditions t 4 (by norm_num) ht
  have hd := (abs_le.mp (sourceLowerTime_log_bound (sourceLowerRadius t) (by linarith))).1
  linarith

/-- The actual source time is negligible compared with the terminal time parameter. -/
theorem sourceLowerTime_div_t_tendsto_zero :
    Tendsto (fun t ↦ sourceLowerTime (sourceLowerRadius t) / t) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ source_lower_time_small_error
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hd := sourceLowerTime_ge_one t ht
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    positivity
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hd := sourceLowerTime_ge_one t ht
    have hl := sourceScaleThreshold_log_lower 4 t ht
    have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
    have hnum : sourceLowerTime (sourceLowerRadius t) ≤
        sourceLowerTime (sourceLowerRadius t) ^ 2 +
          sourceLowerTime (sourceLowerRadius t) * Real.log t := by nlinarith
    have hh := div_le_div_of_nonneg_right hnum (by linarith : 0 ≤ t)
    simpa only [sourceLowerTimeSmallQuantity, add_div] using hh

/-- The uniform diagonal Green scale is negligible compared with t. -/
theorem sourceUniformGreenScale_div_t_tendsto_zero :
    Tendsto (fun t ↦ sourceUniformGreenScale (sourceLowerRadius t) / t) atTop (𝓝 0) := by
  have hlim := sourceLowerTime_div_t_tendsto_zero.const_mul sourceGreenScaleSlope
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hc := sourceScaleThreshold_conditions t 4 (by norm_num) ht
    have hL := (source_uniform_green_bound 0 (sourceLowerRadius t) 14 (by linarith [hc.2.2.1])
      (by norm_num) (by linarith [hc.2.2.1])).1
    exact div_nonneg (by linarith) (by linarith [hc.1])
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hc := sourceScaleThreshold_conditions t 4 (by norm_num) ht
    have hh := div_le_div_of_nonneg_right
      (sourceUniformGreenScale_le_time (sourceLowerRadius t) (sourceLowerTime_ge_one t ht))
      (by linarith [hc.1] : 0 ≤ t)
    simpa only [mul_div_assoc] using hh

end SRWTightness
