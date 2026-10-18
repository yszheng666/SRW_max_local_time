import SRWTightness.TerminalRightWindows

namespace SRWTightness

/-- The terminal exponential varies by at most exp(2) on a GW deficit window. -/
theorem terminal_probability_weight_window (d q q₀ : ℝ) (hd : 0 < d)
    (hq : q ∈ Set.Ioc (q₀ - 1) q₀) :
    Real.exp (-2 * d - 2 * q₀) / d ≤ Real.exp (-2 * d - 2 * q) / d ∧
      Real.exp (-2 * d - 2 * q) / d ≤
        Real.exp 2 * (Real.exp (-2 * d - 2 * q₀) / d) := by
  constructor
  · exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hq.2])) hd.le
  · have hh : Real.exp (-2 * d - 2 * q) ≤ Real.exp 2 * Real.exp (-2 * d - 2 * q₀) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hq.1]
    have hh' := div_le_div_of_nonneg_right hh hd.le
    simpa only [mul_div_assoc] using hh'

end SRWTightness
