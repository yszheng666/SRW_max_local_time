import SRWTightness.SourceLowerTime
import SRWTightness.SourceReferenceIntensity

namespace SRWTightness

theorem sourceOriginGreen_log_bound (m H : ℝ) (hm : 2 ≤ m) (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    |diskGreen (Real.exp 1 * m + H) 0 0 / (2 / Real.pi) - Real.log m| ≤
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 := by
  have hm0 : 0 < m := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hR : 2 ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hb := diskGreen_origin_log_bound (Real.exp 1 * m + H) hR
  have hr1 : 1 ≤ (Real.exp 1 * m + H) / m := by
    apply (le_div_iff₀ hm0).mpr
    nlinarith [Real.exp_one_gt_two]
  have hr4 : (Real.exp 1 * m + H) / m ≤ 4 := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith [Real.exp_one_lt_three]
  have hl0 : 0 ≤ Real.log ((Real.exp 1 * m + H) / m) := Real.log_nonneg hr1
  have hl4 : Real.log ((Real.exp 1 * m + H) / m) ≤ Real.log 4 :=
    Real.log_le_log (by positivity) hr4
  have he : diskGreen (Real.exp 1 * m + H) 0 0 / (2 / Real.pi) - Real.log m =
      (diskGreen (Real.exp 1 * m + H) 0 0 - (2 / Real.pi) * Real.log (Real.exp 1 * m + H)) /
        (2 / Real.pi) + Real.log ((Real.exp 1 * m + H) / m) := by
    rw [Real.log_div (by linarith : Real.exp 1 * m + H ≠ 0) hm0.ne']
    field_simp
    <;> ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add
    (by rw [abs_div, abs_of_pos hg]; exact div_le_div_of_nonneg_right hb hg.le)
    (by simpa only [abs_of_nonneg hl0] using hl4))

end SRWTightness
