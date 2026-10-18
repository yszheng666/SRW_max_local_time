import SRWTightness.DiskDiagonalLogBound

namespace SRWTightness

/-- The actual normalized disk reference variance differs from log radius by a fixed bound. -/
theorem disk_normalized_reference_log_bound (R : ℝ) (hR : 2 ≤ R) :
    |diskGreen R 0 0 / (2 / Real.pi) - Real.log R| ≤
      diskGreenEnergyConstant / (2 / Real.pi) := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have he : diskGreen R 0 0 / (2 / Real.pi) - Real.log R =
      (diskGreen R 0 0 - (2 / Real.pi) * Real.log R) / (2 / Real.pi) := by
    field_simp
    <;> ring
  rw [he, abs_div, abs_of_pos hg]
  exact div_le_div_of_nonneg_right (diskGreen_origin_log_bound R hR) hg.le

/-- A bounded outer-side enlargement preserves the reference depth error. -/
theorem terminal_outer_log_error (R s d B : ℝ) (hR : 0 < R)
    (hRs : R ≤ s) (hs : s ≤ 16 * R) (hb : |d - Real.log R| ≤ B) :
    |d - Real.log s| ≤ B + Real.log 16 := by
  have hlo := Real.log_le_log hR hRs
  have hhi := Real.log_le_log (hR.trans_le hRs) hs
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hR.ne'] at hhi
  have hlog : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hb' := abs_le.mp hb
  rw [abs_le]
  constructor <;> linarith

/-- Fine-square rounding preserves the proportions with an explicit logarithmic margin. -/
theorem terminal_fine_log_proportions (d r s : ℝ) (hr : 0 < r)
    (hrs : r ≤ s) (hs : s ≤ 64 * r)
    (hhL : d / 8 ≤ Real.log r) (hhU : Real.log r + Real.log 64 ≤ d / 2) :
    d / 8 ≤ Real.log s ∧ Real.log s ≤ d / 2 := by
  have hlo := Real.log_le_log hr hrs
  have hhi := Real.log_le_log (hr.trans_le hrs) hs
  rw [Real.log_mul (by norm_num : (64 : ℝ) ≠ 0) hr.ne'] at hhi
  constructor <;> linarith

end SRWTightness
