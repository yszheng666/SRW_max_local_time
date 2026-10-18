import SRWTightness.AnnulusPotentialComparison
import SRWTightness.DiskGreenEnergyBounds

namespace SRWTightness

theorem annulusOuterExitProbability_nonneg (a R : ℝ) (x : Site) :
    0 ≤ annulusOuterExitProbability a R x := ENNReal.toReal_nonneg

/-- Escape from a point at most one step beyond the double-radius circle.
This upper bound does not require the unproved fine potential-kernel asymptotic. -/
theorem annulusOuterExitProbability_log_upper (a R : ℝ) (ha : 4 ≤ a) (hRa : a < R)
    (x : Site) (hxlo : a ^ 2 ≤ normSq x) (hxhi : normSq x ≤ (2 * a + 1) ^ 2) :
    annulusOuterExitProbability a R x ≤
      diskGreenEnergyConstant / ((2 / Real.pi) * Real.log (R / a)) := by
  have ha0 : 0 < a := by linarith
  have ham : 0 < a - 1 := by linarith
  have hR : 0 < R := ha0.trans hRa
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hlogpos : 0 < Real.log (R / a) := Real.log_pos ((one_lt_div ha0).mpr hRa)
  have hp := annulusOuterExitProbability_nonneg a R x
  have hmain := annulusOuterExitProbability_potential_bound a R ha hRa.le x hxlo
  have hu := potentialKernel_radius_upper x (2 * a + 1) (by linarith) hxhi
  have hfrac : (2 * a + 1) / (a - 1) ≤ 3 := by
    apply (div_le_iff₀ ham).mpr
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < (2 * a + 1) / (a - 1)) hfrac
  rw [Real.log_div (by linarith : 2 * a + 1 ≠ 0) ham.ne'] at hlog
  have hl := mul_le_mul_of_nonneg_left hlog hg.le
  have hla := Real.log_le_log ham (by linarith : a - 1 ≤ a)
  have hc : (2 / Real.pi) * Real.log (R / a) * annulusOuterExitProbability a R x ≤
      (2 / Real.pi) * (Real.log R - Real.log (a - 1)) * annulusOuterExitProbability a R x := by
    apply mul_le_mul_of_nonneg_right _ hp
    apply mul_le_mul_of_nonneg_left _ hg.le
    rw [Real.log_div hR.ne' ha0.ne']
    linarith
  have htwo : 0 ≤ (2 / Real.pi) * Real.log 2 :=
    mul_nonneg hg.le (Real.log_nonneg (by norm_num))
  have hn : potentialKernel x - ((2 / Real.pi) * Real.log (a - 1) - potentialLowerConstant) ≤
      diskGreenEnergyConstant := by
    unfold diskGreenEnergyConstant
    nlinarith
  have hb := hc.trans (hmain.trans hn)
  apply (le_div_iff₀ (mul_pos hg hlogpos)).mpr
  simpa only [mul_comm] using hb

end SRWTightness
