import SRWTightness.SourceTerminalThresholdUniform
import SRWTightness.SourceGreenScaleComparison

namespace SRWTightness

/-- Exact integer generation count in the lower construction. -/
noncomputable def sourceCoarseGeneration (t : ℝ) : ℤ :=
  Int.floor (t - Real.log 32 - sourceLowerLogRadius t) - 1

noncomputable def sourceTotalTime (t : ℝ) : ℝ :=
  (sourceCoarseGeneration t : ℝ) + sourceLowerTime (sourceLowerRadius t)

noncomputable def sourceTotalTimeError : ℝ := 2 + Real.log 32 + sourceLowerTimeError

noncomputable def sourceBarrierSlope (t : ℝ) : ℝ := sourceTerminalHeight t / sourceTotalTime t

theorem sourceCoarseGeneration_at_radius (R : ℝ) (hR : 0 < R) :
    sourceCoarseGeneration (Real.log R) =
      Int.floor (Real.log (R / (32 * sourceLowerRadius (Real.log R)))) - 1 := by
  have he : Real.log (R / (32 * sourceLowerRadius (Real.log R))) =
      Real.log R - Real.log 32 - sourceLowerLogRadius (Real.log R) := by
    rw [Real.log_div hR.ne' (mul_ne_zero (by norm_num) (sourceLowerRadius_pos _).ne'),
      Real.log_mul (by norm_num) (sourceLowerRadius_pos _).ne',
      log_sourceLowerRadius]
    ring
  rw [he]
  rfl

theorem sourceTotalTimeError_pos : 0 < sourceTotalTimeError := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 32)
  have he := sourceLowerTimeError_pos
  unfold sourceTotalTimeError
  positivity

/-- The exact floor and the actual Green-function time give a uniform bounded total-time error. -/
theorem sourceTotalTime_error (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t) :
    |sourceTotalTime t - t| ≤ sourceTotalTimeError := by
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  have hd := sourceLowerTime_log_bound (sourceLowerRadius t) (by linarith)
  rw [log_sourceLowerRadius] at hd
  have hf := Int.floor_le (t - Real.log 32 - sourceLowerLogRadius t)
  have hf' := Int.lt_floor_add_one (t - Real.log 32 - sourceLowerLogRadius t)
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 32)
  obtain ⟨hdl, hdu⟩ := abs_le.mp hd
  unfold sourceTotalTime sourceCoarseGeneration sourceTotalTimeError
  push_cast
  apply abs_le.mpr
  constructor <;> linarith

/-- Explicit large-time lower bound for the denominator of the barrier slope. -/
theorem sourceTotalTime_ge_half (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t) : t / 2 ≤ sourceTotalTime t := by
  have hh := (abs_le.mp (sourceTotalTime_error t ht)).1
  linarith

theorem sourceBarrierSlope_bounds (t : ℝ) (ht : sourceScaleThreshold 4 ≤ t)
    (htE : 2 * sourceTotalTimeError ≤ t) :
    0 ≤ sourceBarrierSlope t ∧ sourceBarrierSlope t ≤ 4 := by
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have ht0 : 0 < t := by linarith
  have hT := sourceTotalTime_ge_half t ht htE
  have hT0 : 0 < sourceTotalTime t := by linarith
  have hl := Real.log_nonneg (show 1 ≤ t by linarith)
  have hu := Real.log_le_sub_one_of_pos ht0
  unfold sourceBarrierSlope sourceTerminalHeight
  constructor
  · exact div_nonneg (by linarith) hT0.le
  · apply (div_le_iff₀ hT0).mpr
    linarith

end SRWTightness
