import SRWTightness.CenteringAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter

namespace SRWTightness

theorem log_radius_le_diskCenter (R : ℝ) (hR : 1 < R) :
    Real.log R / Real.sqrt Real.pi ≤ diskCenter R := by
  have hl := Real.log_le_sub_one_of_pos (Real.log_pos hR)
  unfold diskCenter
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith

theorem diskCenter_pos (R : ℝ) (hR : 1 < R) : 0 < diskCenter R :=
  (div_pos (Real.log_pos hR) (Real.sqrt_pos.mpr Real.pi_pos)).trans_le
    (log_radius_le_diskCenter R hR)

theorem diskCenter_tendsto_atTop : Tendsto diskCenter atTop atTop := by
  apply tendsto_atTop_mono' atTop _
    (Real.tendsto_log_atTop.atTop_div_const (Real.sqrt_pos.mpr Real.pi_pos))
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  exact log_radius_le_diskCenter R hR

end SRWTightness
