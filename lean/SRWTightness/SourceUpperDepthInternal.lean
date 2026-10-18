import SRWTightness.ExponentialFloorScaleProof
import SRWTightness.SourceUpperDepthLogLimit

open Filter
open scoped Topology
namespace SRWTightness

/-- The actual total depth has bounded drift with no external scale input. -/
theorem source_upper_total_depth_internal :
    ∀ᶠ t : ℝ in atTop, |sourceUpperTotalDepth t - t| ≤
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 32 + 4 :=
  source_upper_total_depth_eventually exponential_floor_scale_input

/-- The actual Green depth has bounded logarithmic error with no scale premise. -/
theorem source_upper_terminal_depth_internal :
    ∀ᶠ t : ℝ in atTop,
      |upperTerminalDepth (sourceUpperLogRadius t) - sourceUpperLogRadius t| ≤
        diskGreenEnergyConstant / (2 / Real.pi) + 2 :=
  source_upper_terminal_depth_eventually exponential_floor_scale_input

/-- All logarithmic power weights of the actual Green depth are negligible against t. -/
theorem source_upper_depth_log_power_internal (n : ℕ) :
    Tendsto (fun t : ℝ ↦
      upperTerminalDepth (sourceUpperLogRadius t) * (Real.log t) ^ n / t) atTop (𝓝 0) :=
  source_upper_depth_log_power_limit exponential_floor_scale_input n

/-- The square of the actual Green depth is negligible against the logarithmic outer radius. -/
theorem source_upper_depth_square_internal :
    Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) ^ 2 / t)
      atTop (𝓝 0) := by
  let B : ℝ := diskGreenEnergyConstant / (2 / Real.pi) + 2
  have hlim : Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) *
      (sourceUpperLogRadius t + B) / t) atTop (𝓝 0) := by
    have hh := ((source_upper_depth_log_power_internal 4).const_mul (8 ^ 4 : ℝ)).add
      ((source_upper_depth_log_power_internal 0).const_mul B)
    convert hh using 1
    · funext t
      simp only [sourceUpperLogRadius, mul_pow, pow_zero, mul_one]
      ring
    · simp
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact div_nonneg (sq_nonneg _) (by linarith)
  · filter_upwards [source_upper_terminal_depth_internal,
      eventually_ge_atTop (1 : ℝ)] with t hd ht
    have hnonneg : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
      unfold upperTerminalDepth diskGreen
      exact div_nonneg (killedGreen_nonneg _ _ _) (by positivity)
    have hup : upperTerminalDepth (sourceUpperLogRadius t) ≤ sourceUpperLogRadius t + B := by
      have hh := (abs_le.mp hd).2
      dsimp [B]
      linarith
    apply div_le_div_of_nonneg_right ?_ (by linarith : 0 ≤ t)
    nlinarith

end SRWTightness
