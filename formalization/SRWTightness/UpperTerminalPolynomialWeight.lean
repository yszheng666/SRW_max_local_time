import SRWTightness.UpperTerminalRoundedTilt

namespace SRWTightness

/-- The terminal-window polynomial is controlled by one normalized quadratic Gaussian weight. -/
theorem upper_terminal_polynomial_scaled (A z : ℝ) (hA : 0 ≤ A) (hz : 0 ≤ z) :
    (A + z) * (1 + z) ≤ 2 * (A + 1) * (1 + z ^ 2) := by
  nlinarith [sq_nonneg (z - 1), mul_nonneg hA (sq_nonneg (z - 1)),
    mul_nonneg hA (sq_nonneg z)]

/-- Positive terminal-window weights have the correct inverse-square-root scale. -/
theorem upper_terminal_polynomial_weight (d S q : ℝ)
    (hd : 0 < d) (hS : 0 ≤ S) (hq : 0 ≤ q) :
    (S + q) * (1 + q / Real.sqrt d) / d ≤
      2 * (1 + S / Real.sqrt d) * (1 + (q / Real.sqrt d) ^ 2) / Real.sqrt d := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hp := div_le_div_of_nonneg_right
    (upper_terminal_polynomial_scaled (S / Real.sqrt d) (q / Real.sqrt d)
      (div_nonneg hS hs.le) (div_nonneg hq hs.le)) hs.le
  calc
    _ = (S + q) * (1 + q / Real.sqrt d) / (Real.sqrt d) ^ 2 :=
      congrArg (fun v : ℝ ↦ (S + q) * (1 + q / Real.sqrt d) / v)
        (Real.sq_sqrt hd.le).symm
    _ = (S / Real.sqrt d + q / Real.sqrt d) *
        (1 + q / Real.sqrt d) / Real.sqrt d := by field_simp [hs.ne'] <;> ring
    _ ≤ 2 * (S / Real.sqrt d + 1) * (1 + (q / Real.sqrt d) ^ 2) / Real.sqrt d := hp
    _ = _ := by ring

end SRWTightness
