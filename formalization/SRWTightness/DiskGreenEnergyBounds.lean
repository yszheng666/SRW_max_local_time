import SRWTightness.DiskExitPotentialLower
import SRWTightness.DiskOnePoint

namespace SRWTightness

noncomputable def diskGreenEnergyConstant : ℝ :=
  (2 / Real.pi) * (Real.log 3 + Real.log 2) + potentialUpperConstant + potentialLowerConstant

theorem diskGreenEnergyConstant_pos : 0 < diskGreenEnergyConstant := by
  unfold diskGreenEnergyConstant
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hU := potentialUpperConstant_pos
  have hL := potentialLowerConstant_pos
  positivity

theorem diskGreen_inner_lower (R a : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R) (y : Site) (hy : y ∈ disk a) :
    (2 / Real.pi) * Real.log (R / a) - diskGreenEnergyConstant ≤ diskGreen R 0 y := by
  have hR : 0 < R := by linarith
  have ha0 : 0 < a := by linarith
  have hy' : normSq y ≤ a ^ 2 := (show normSq y < a ^ 2 from hy).le
  have hinner : normSq y ≤ (R / 2) ^ 2 := by nlinarith
  have hl := exitPayoff_potential_disk_lower R hR y hinner
  have hu := potentialKernel_le_log_normBound y (a ^ 2) (by nlinarith) hy'
  unfold diskGreen
  rw [potentialKernel_green_representation, zero_sub, potentialKernel_neg]
  have he : (2 / Real.pi) * Real.log (R / 2) - Real.log (a ^ 2) / Real.pi =
      (2 / Real.pi) * Real.log (R / a) - (2 / Real.pi) * Real.log 2 := by
    rw [Real.log_div hR.ne' (by norm_num), Real.log_pow, Real.log_div hR.ne' ha0.ne']
    ring
  unfold diskGreenEnergyConstant
  have h3 : 0 ≤ (2 / Real.pi) * Real.log 3 := mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  nlinarith

theorem diskGreen_inner_radius_upper (R a : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R) (y : Site)
    (hy : y ∈ disk a) (hs : a / 2 ≤ max (Real.sqrt (normSq y)) 1) :
    diskGreen R 0 y ≤ (2 / Real.pi) * Real.log (R / a) + diskGreenEnergyConstant := by
  have hR : 0 < R := by linarith
  have ha0 : 0 < a := by linarith
  have hyR : y ∈ disk R := by change normSq y < R ^ 2; have hh : normSq y < a ^ 2 := hy; nlinarith
  have hu := exitPayoff_potential_disk_upper R (by linarith) y hyR
  have hlog := Real.log_le_log (by positivity : 0 < a / 2) hs
  have hp := potentialKernel_ge_log_radius y
  have hlog' := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / Real.pi)
  unfold diskGreen
  rw [potentialKernel_green_representation, zero_sub, potentialKernel_neg]
  have he : Real.log ((3 * R) ^ 2) / Real.pi - (2 / Real.pi) * Real.log (a / 2) =
      (2 / Real.pi) * Real.log (R / a) + (2 / Real.pi) * (Real.log 3 + Real.log 2) := by
    rw [Real.log_pow, Real.log_mul (by norm_num) hR.ne', Real.log_div ha0.ne' (by norm_num),
      Real.log_div hR.ne' ha0.ne']
    ring
  unfold diskGreenEnergyConstant
  linarith

theorem diskGreen_inner_shell_upper (R a : ℝ) (ha : 2 ≤ a) (hRa : 2 * a ≤ R) (y : Site)
    (hy : y ∈ disk a) (hyl : (a - 1) ^ 2 ≤ normSq y) :
    diskGreen R 0 y ≤ (2 / Real.pi) * Real.log (R / a) + diskGreenEnergyConstant := by
  apply diskGreen_inner_radius_upper R a (by linarith) hRa y hy
  have hs : a / 2 ≤ Real.sqrt (normSq y) := by
    apply (Real.le_sqrt (by linarith) (normSq_nonneg y)).mpr
    nlinarith
  exact hs.trans (le_max_left _ _)

end SRWTightness
