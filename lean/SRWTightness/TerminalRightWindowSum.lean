import SRWTightness.TerminalRightWindows

open scoped BigOperators

namespace SRWTightness

/-- Weight at right endpoints of the complete deficit windows used for the lower bound. -/
noncomputable def terminalRightInnerWeight (d : ℝ) : ℝ :=
  ∑ i ∈ Finset.range ⌊Real.sqrt d⌋₊, (1 + (terminalWindowLeft d i + 1))

/-- Covering weight, including a final window with right endpoint exactly at the band edge. -/
noncomputable def terminalRightOuterWeight (d : ℝ) : ℝ :=
  terminalOuterWindowWeight d + (1 + 2 * Real.sqrt d)

/-- Right-endpoint weights retain a uniform lower bound after normalization. -/
theorem terminal_right_inner_weight_lower (d : ℝ) (hd : 4 ≤ d) :
    (1 / 2 : ℝ) ≤ terminalRightInnerWeight d / d := by
  have hh : terminalInnerWindowWeight d ≤ terminalRightInnerWeight d := by
    unfold terminalInnerWindowWeight terminalRightInnerWeight
    apply Finset.sum_le_sum
    intro i hi
    linarith
  have hl := terminal_inner_window_weight_lower d hd
  apply (le_div_iff₀ (show 0 < d by linarith)).mpr
  linarith

/-- The extra covering window contributes only a bounded amount to the normalized weight. -/
theorem terminal_right_outer_weight_upper (d : ℝ) (hd : 4 ≤ d) :
    terminalRightOuterWeight d / d ≤ 9 := by
  have hh := terminal_outer_window_weight_upper d hd
  have hs0 := Real.sqrt_nonneg d
  have hs := Real.sq_sqrt (show 0 ≤ d by linarith)
  have hsd : Real.sqrt d ≤ d := by nlinarith
  apply (div_le_iff₀ (show 0 < d by linarith)).mpr
  unfold terminalRightOuterWeight
  linarith

end SRWTightness
