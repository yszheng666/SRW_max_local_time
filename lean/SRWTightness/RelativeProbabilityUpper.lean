import SRWTightness.RelativeProbabilityExponential

namespace SRWTightness

/-- Relative probability errors give an exponential upper bound without a smallness restriction. -/
theorem relative_probability_exponential_upper (p q ε : ℝ) (hq : 0 ≤ q)
    (hp : |p - q| ≤ ε * q) : p ≤ Real.exp ε * q := by
  have hu := (abs_le.mp hp).2
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp ε) hq
  nlinarith

end SRWTightness
