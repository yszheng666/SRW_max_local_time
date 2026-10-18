import SRWTightness.UpperTerminalGaussianIntegral

namespace SRWTightness

/-- Nearby nonnegative window coordinates admit a broadened Gaussian integral majorant. -/
theorem upper_terminal_gaussian_window (d c q x : ℝ)
    (hd : 1 ≤ d) (hc : 0 < c) (hq : 0 ≤ q) (hx : 0 ≤ x)
    (hqx : |q - x| ≤ 1) :
    upperTerminalGaussianKernel d c q ≤
      (3 * Real.exp c) * upperTerminalGaussianKernel d (c / 2) x := by
  have hd0 : 0 < d := by linarith
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hab := abs_le.mp hqx
  have hdiff : (q - x) ^ 2 ≤ 1 := by nlinarith
  have hq2 : q ^ 2 ≤ 2 * x ^ 2 + 2 := by
    nlinarith [sq_nonneg (x - (q - x))]
  have hx2 : x ^ 2 ≤ 2 * q ^ 2 + 2 := by
    nlinarith [sq_nonneg (q - (x - q))]
  have hinv : 1 / d ≤ 1 := (div_le_one hd0).mpr hd
  have hdiv := div_le_div_of_nonneg_right hq2 hd0.le
  have hdivid : (2 * x ^ 2 + 2) / d = 2 * (x ^ 2 / d) + 2 * (1 / d) := by ring
  rw [hdivid] at hdiv
  have hp : 1 + q ^ 2 / d ≤ 3 * (1 + x ^ 2 / d) := by
    nlinarith [div_nonneg (sq_nonneg x) hd0.le]
  have he0 : c * x ^ 2 / (2 * d) ≤ c * q ^ 2 / d + c / d := by
    convert div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx2 hc.le)
      (by positivity : 0 ≤ 2 * d) using 1 <;> first | rfl | ring
  have hcdiv : c / d ≤ c := (div_le_iff₀ hd0).mpr (by nlinarith)
  have he : -c * q ^ 2 / d ≤ c + -(c / 2) * x ^ 2 / d := by
    have hid : c * x ^ 2 / (2 * d) = (c / 2) * x ^ 2 / d := by ring
    rw [hid] at he0
    linear_combination he0 + hcdiv
  have hpoly : (1 + (q / Real.sqrt d) ^ 2) / Real.sqrt d ≤
      3 * ((1 + (x / Real.sqrt d) ^ 2) / Real.sqrt d) := by
    have hid (y : ℝ) : (y / Real.sqrt d) ^ 2 = y ^ 2 / d := by
      rw [div_pow, Real.sq_sqrt hd0.le]
    rw [hid q, hid x]
    convert div_le_div_of_nonneg_right hp hs.le using 1 <;> first | rfl | ring
  unfold upperTerminalGaussianKernel
  apply (mul_le_mul hpoly (Real.exp_le_exp.mpr he) (Real.exp_nonneg _)
    (by positivity)).trans_eq
  rw [Real.exp_add]
  ring

end SRWTightness
