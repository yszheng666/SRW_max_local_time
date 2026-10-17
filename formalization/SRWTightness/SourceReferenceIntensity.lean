import SRWTightness.CapacityEnergyParameters

namespace SRWTightness

noncomputable def sourceReferenceIntensity (m H : ℝ) : ℝ :=
  (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))

/-- Explicit large-m conditions for the original terminal reference intensity. -/
theorem sourceReferenceIntensity_bounds (m H : ℝ) (hm : 0 < m) (hH : 0 ≤ H)
    (hHm : 5 * H ≤ m) : 0 < sourceReferenceIntensity m H ∧
      sourceReferenceIntensity m H ≤ 2 * (2 / Real.pi) := by
  have hd : 0 < m - H := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hr1 : 1 < (Real.exp 1 * m + H) / (m - H) := by
    apply (one_lt_div hd).mpr
    nlinarith [Real.exp_one_gt_two]
  have hr4 : (Real.exp 1 * m + H) / (m - H) ≤ 4 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [Real.exp_one_lt_three]
  have hl4 := Real.log_le_log (by linarith : 0 < (Real.exp 1 * m + H) / (m - H)) hr4
  have he4 : (4 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hlog4 : Real.log 4 < 2 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr he4
  unfold sourceReferenceIntensity
  constructor
  · exact mul_pos hg (Real.log_pos hr1)
  · have hh := mul_le_mul_of_nonneg_left (hl4.trans hlog4.le) hg.le
    simpa only [mul_comm] using hh

end SRWTightness
