import SRWTightness.DiskDiagonalLogBound
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SRWTightness

/-- The exact d in the lower-tail construction, with killing radius e*m-1. -/
noncomputable def sourceLowerTime (m : ℝ) : ℝ :=
  diskGreen (Real.exp 1 * m - 1) 0 0 / (2 / Real.pi)

noncomputable def sourceLowerTimeError : ℝ :=
  diskGreenEnergyConstant / (2 / Real.pi) + Real.log 3

theorem sourceLowerTimeError_pos : 0 < sourceLowerTimeError := by
  unfold sourceLowerTimeError
  exact add_pos (div_pos diskGreenEnergyConstant_pos (by positivity))
    (Real.log_pos (by norm_num))

theorem sourceLowerTime_log_bound (m : ℝ) (hm : 2 ≤ m) :
    |sourceLowerTime m - Real.log m| ≤ sourceLowerTimeError := by
  have hm0 : 0 < m := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hR : 2 ≤ Real.exp 1 * m - 1 := by nlinarith [Real.exp_one_gt_two]
  have hb := diskGreen_origin_log_bound (Real.exp 1 * m - 1) hR
  have hr1 : 1 ≤ (Real.exp 1 * m - 1) / m := by
    apply (le_div_iff₀ hm0).mpr
    nlinarith [Real.exp_one_gt_two]
  have hr3 : (Real.exp 1 * m - 1) / m ≤ 3 := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith [Real.exp_one_lt_three]
  have hl0 : 0 ≤ Real.log ((Real.exp 1 * m - 1) / m) := Real.log_nonneg hr1
  have hl3 : Real.log ((Real.exp 1 * m - 1) / m) ≤ Real.log 3 :=
    Real.log_le_log (by positivity) hr3
  have he : sourceLowerTime m - Real.log m =
      (diskGreen (Real.exp 1 * m - 1) 0 0 - (2 / Real.pi) * Real.log (Real.exp 1 * m - 1)) /
        (2 / Real.pi) + Real.log ((Real.exp 1 * m - 1) / m) := by
    rw [Real.log_div (by linarith : Real.exp 1 * m - 1 ≠ 0) hm0.ne']
    unfold sourceLowerTime
    field_simp
    <;> ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_div, abs_of_pos hg]
    exact div_le_div_of_nonneg_right hb hg.le
  · simpa only [abs_of_nonneg hl0] using hl3

end SRWTightness
