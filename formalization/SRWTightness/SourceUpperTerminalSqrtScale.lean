import SRWTightness.SourceUpperDepthLogLimit

open Filter

namespace SRWTightness

/-- The terminal square-root depth eventually dominates the logarithmic height range. -/
theorem source_upper_terminal_sqrt_scale (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, 1 ≤ Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) ∧
      Real.log t ≤ Real.sqrt (upperTerminalDepth (sourceUpperLogRadius t)) := by
  let D : ℝ := diskGreenEnergyConstant / (2 / Real.pi) + 2
  filter_upwards [source_upper_terminal_depth_eventually hScale,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (D + 1)))] with t hd hl
  have hx : 1 ≤ Real.log t := (le_max_left _ _).trans hl
  have hxD : D + 1 ≤ Real.log t := (le_max_right _ _).trans hl
  have hD : 0 ≤ D := (abs_nonneg _).trans hd
  have hx0 : 0 ≤ Real.log t := by linarith
  have hx2 : 1 ≤ (Real.log t) ^ 2 := by nlinarith
  have hx4 : (Real.log t) ^ 2 ≤ (Real.log t) ^ 4 := by
    nlinarith [sq_nonneg ((Real.log t) ^ 2 - 1)]
  have hlow := (abs_le.mp hd).1
  change -D ≤ upperTerminalDepth (sourceUpperLogRadius t) - sourceUpperLogRadius t at hlow
  change -D ≤ upperTerminalDepth (sourceUpperLogRadius t) - (8 * Real.log t) ^ 4 at hlow
  have hdlog : (Real.log t) ^ 2 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    nlinarith [sq_nonneg (Real.log t - 1)]
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) :=
    (sq_nonneg _).trans hdlog
  have hs0 := Real.sqrt_nonneg (upperTerminalDepth (sourceUpperLogRadius t))
  have hsq := Real.sq_sqrt hd0
  constructor <;> nlinarith

end SRWTightness
