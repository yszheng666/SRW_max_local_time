import SRWTightness.SourceUpperTerminalTiltError

open Filter
open scoped Topology

namespace SRWTightness

/-- The squared actual-target tilt majorant is negligible at terminal depth. -/
theorem source_upper_terminal_tilt_square_limit (hScale : ExponentialFloorScaleInput)
    (B : ℝ) :
    Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) *
      (((8 + 2 * Real.sqrt Real.pi) * Real.log t + 4 * B + 6) / t) ^ 2)
      atTop (𝓝 0) := by
  let a : ℝ := 8 + 2 * Real.sqrt Real.pi
  let b : ℝ := 4 * B + 6
  have h0 := source_upper_depth_log_power_limit hScale 0
  have h1 := source_upper_depth_log_power_limit hScale 1
  have h2 := source_upper_depth_log_power_limit hScale 2
  have hi : Tendsto (fun t : ℝ ↦ 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
  have hh := ((h2.const_mul (a ^ 2)).add
    ((h1.const_mul (2 * a * b)).add (h0.const_mul (b ^ 2)))).mul hi
  convert hh using 1
  · funext t
    dsimp [a, b]
    simp only [pow_zero, pow_one, mul_one]
    ring
  · simp

end SRWTightness
