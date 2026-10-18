import SRWTightness.SourceUpperDepthLogLimit

open Filter
open scoped Topology

namespace SRWTightness

/-- The explicit baseline error used in the one-sided exponential normalization. -/
noncomputable def sourceUpperBaselineError (t B : ℝ) : ℝ :=
  2 * (6 + Real.sqrt Real.pi) * upperTerminalDepth (sourceUpperLogRadius t) *
    ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / t

/-- The baseline error vanishes at the actual source scale. -/
theorem source_upper_baseline_error_limit (hScale : ExponentialFloorScaleInput) (B : ℝ) :
    Tendsto (fun t : ℝ ↦ sourceUpperBaselineError t B) atTop (𝓝 0) := by
  have hh := ((source_upper_depth_log_power_limit hScale 1).const_mul
    (2 * (6 + Real.sqrt Real.pi) * (1 + Real.sqrt Real.pi))).add
    ((source_upper_depth_log_power_limit hScale 0).const_mul
      (4 * (6 + Real.sqrt Real.pi) * B))
  convert hh using 1
  · funext t
    simp only [sourceUpperBaselineError, pow_one, pow_zero, mul_one]
    ring
  · simp

end SRWTightness
