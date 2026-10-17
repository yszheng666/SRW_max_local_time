import SRWTightness.UpperTerminalQuadraticTilt

namespace SRWTightness

/-- A positive terminal deficit retains Gaussian decay after both tilt and unit rounding. -/
theorem upper_terminal_positive_rounded_tilt (d c β q : ℝ)
    (hd : 0 < d) (hc : 0 < c) (hq : 0 ≤ q) :
    β * q - c * (max (q - 1) 0) ^ 2 / d ≤
      c / d + 2 * d * β ^ 2 / c - 3 * c * q ^ 2 / (8 * d) := by
  have hr := upper_terminal_rounded_square q
  rw [max_eq_left hq] at hr
  have hp : 0 ≤ c * (2 * (max (q - 1) 0) ^ 2 + 2 - q ^ 2) / (2 * d) := by
    apply div_nonneg (mul_nonneg hc.le (by linarith)) (by positivity)
  have he : c / d - c * q ^ 2 / (2 * d) + c * (max (q - 1) 0) ^ 2 / d =
      c * (2 * (max (q - 1) 0) ^ 2 + 2 - q ^ 2) / (2 * d) := by ring
  rw [← he] at hp
  have hy : β * q - c * q ^ 2 / (2 * d) ≤
      2 * d * β ^ 2 / c - 3 * c * q ^ 2 / (8 * d) := by
    convert upper_terminal_quadratic_tilt d (c / 2) β q hd (by positivity) using 1 <;> ring
  linarith

/-- The full terminal deficit range adds only a bounded cost for its negative portion. -/
theorem upper_terminal_rounded_tilt (d c β q Q : ℝ)
    (hd : 0 < d) (hc : 0 < c) (hQ : 0 ≤ Q) (hq : -Q ≤ q) :
    β * q - c * (max (q - 1) 0) ^ 2 / d ≤
      c / d + 2 * d * β ^ 2 / c + |β| * Q -
        3 * c * (max q 0) ^ 2 / (8 * d) := by
  by_cases h : 0 ≤ q
  · rw [max_eq_left h]
    have hh := upper_terminal_positive_rounded_tilt d c β q hd hc h
    linarith [mul_nonneg (abs_nonneg β) hQ]
  · rw [max_eq_right (by linarith : q - 1 ≤ 0), max_eq_right (by linarith : q ≤ 0)]
    have hm := mul_le_mul_of_nonneg_right (neg_le_abs β) (by linarith : 0 ≤ -q)
    have hn := mul_le_mul_of_nonneg_left (show -q ≤ Q by linarith) (abs_nonneg β)
    have hp : 0 ≤ c / d := div_nonneg hc.le hd.le
    have hj : 0 ≤ 2 * d * β ^ 2 / c := by positivity
    norm_num only [zero_pow, mul_zero, zero_div, sub_zero] at *
    nlinarith

end SRWTightness
