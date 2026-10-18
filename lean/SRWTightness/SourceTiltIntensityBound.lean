import SRWTightness.SourceUniformGreenBound
import SRWTightness.SourceReferenceIntensity

namespace SRWTightness

/-- The actual terminal reference intensity stays above the fixed planar Green constant. -/
theorem sourceReferenceIntensity_ge_greenConstant (m H : ℝ) (hm : 0 < m)
    (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    (2 / Real.pi : ℝ) ≤ sourceReferenceIntensity m H := by
  have hd : 0 < m - H := by linarith
  have hr : Real.exp 1 ≤ (Real.exp 1 * m + H) / (m - H) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hl := Real.log_le_log (Real.exp_pos (1 : ℝ)) hr
  rw [Real.log_exp] at hl
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (2 / Real.pi : ℝ))
  simpa only [sourceReferenceIntensity, mul_one] using hh

/-- The source intensity meets the hypothesis of the uniform tilted-moment estimates. -/
theorem sourceReferenceIntensity_le_uniformGreenScale (m H : ℝ) (hm : 9 ≤ m)
    (hH : 0 ≤ H) (hHm : 5 * H ≤ m) :
    sourceReferenceIntensity m H ≤ sourceUniformGreenScale m := by
  have hm0 : 0 < m := by linarith
  have hα := (sourceReferenceIntensity_bounds m H hm0 hH hHm).2
  have he : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 : ℝ)]
  have hl : 2 ≤ Real.log m := (Real.le_log_iff_exp_le hm0).mpr (he.le.trans hm)
  have hd := (abs_le.mp (sourceLowerTime_log_bound m (by linarith))).1
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have ht := mul_le_mul_of_nonneg_left
    (show Real.log m ≤ sourceLowerTime m + sourceLowerTimeError by linarith) hg.le
  have h2 := mul_le_mul_of_nonneg_left hl hg.le
  have hlogs : 0 ≤ (2 / Real.pi : ℝ) * (Real.log 4 + Real.log 2) :=
    mul_nonneg hg.le (add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num)))
  have hB := diskGreenEnergyConstant_pos.le
  unfold sourceUniformGreenScale
  linarith

end SRWTightness
