import SRWTightness.SourceCoarseTime

open Filter
open scoped Topology

namespace SRWTightness

theorem sourceBarrierSlope_error (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t) :
    |sourceBarrierSlope t - 2| ≤ 2 * (2 * sourceTotalTimeError + Real.log t) / t := by
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hT := sourceTotalTime_ge_half t ht htE
  have hT0 : 0 < sourceTotalTime t := by linarith
  have hl := Real.log_nonneg (show 1 ≤ t by linarith)
  have hE := sourceTotalTimeError_pos
  have herr := abs_le.mp (sourceTotalTime_error t ht)
  have he : sourceBarrierSlope t - 2 =
      (2 * t - Real.log t - 2 * sourceTotalTime t) / sourceTotalTime t := by
    unfold sourceBarrierSlope sourceTerminalHeight
    field_simp
  rw [he, abs_div, abs_of_pos hT0]
  have hn : |2 * t - Real.log t - 2 * sourceTotalTime t| ≤
      2 * sourceTotalTimeError + Real.log t := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ (2 * sourceTotalTimeError + Real.log t) / sourceTotalTime t :=
      div_le_div_of_nonneg_right hn hT0.le
    _ ≤ (2 * sourceTotalTimeError + Real.log t) / (t / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hT
    _ = _ := by ring

theorem sourceBarrierSlope_weighted_error (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t) :
    |sourceBarrierSlope t - 2| * sourceLowerTime (sourceLowerRadius t) ≤
      4 * sourceTotalTimeError * (sourceLowerTime (sourceLowerRadius t) / t) +
        2 * sourceLowerTimeSmallQuantity t := by
  have hd := sourceLowerTime_ge_one t ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hh := mul_le_mul_of_nonneg_right (sourceBarrierSlope_error t ht htE)
    (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)
  have hsq : 0 ≤ sourceLowerTime (sourceLowerRadius t) ^ 2 / t := by positivity
  unfold sourceLowerTimeSmallQuantity
  calc
    _ ≤ (2 * (2 * sourceTotalTimeError + Real.log t) / t) *
        sourceLowerTime (sourceLowerRadius t) := hh
    _ = 4 * sourceTotalTimeError * (sourceLowerTime (sourceLowerRadius t) / t) +
        2 * (sourceLowerTime (sourceLowerRadius t) * Real.log t / t) := by ring
    _ ≤ _ := by linarith [hsq]

theorem sourceBarrierSlope_weighted_tendsto_zero :
    Tendsto (fun t : ℝ ↦ |sourceBarrierSlope t - 2| *
      sourceLowerTime (sourceLowerRadius t)) atTop (𝓝 0) := by
  have hh := (sourceLowerTime_div_t_tendsto_zero.const_mul (4 * sourceTotalTimeError)).add
    (source_lower_time_small_error.const_mul 2)
  simp only [mul_zero, add_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4)] with t ht
    have hd := sourceLowerTime_ge_one t ht
    exact mul_nonneg (abs_nonneg _) (by linarith)
  · filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4),
      eventually_ge_atTop (2 * sourceTotalTimeError)] with t ht htE
    exact sourceBarrierSlope_weighted_error t ht htE

end SRWTightness
