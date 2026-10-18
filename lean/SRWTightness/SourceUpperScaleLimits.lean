import SRWTightness.SourceUpperRemainingLimits
import SRWTightness.SourceUpperQuarterRoot
import SRWTightness.SourceUpperMeshExponential

open Filter
open scoped Topology
namespace SRWTightness

/-- All five source (4.3) limits, at the original real radius and with actual Green depth. -/
theorem source_upper_scale_limits :
    Tendsto (fun R : ℝ ↦
      upperTerminalDepth (sourceUpperLogRadius (Real.log R)) ^ (1 / 4 : ℝ) -
        8 * Real.log (Real.log R)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius (Real.log R)) ^ 2 /
      Real.log R) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius (Real.log R)) *
      Real.log (Real.log R) / Real.log R) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ ↦ (Real.log R) ^ 2 * sourceUpperLogRadius (Real.log R) *
      Real.exp (-3 * sourceUpperLogRadius (Real.log R) / 4)) atTop (𝓝 0) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun R : ℝ ↦ R ^ 2 *
      Real.exp (-c * (Real.log R) ^ 2 /
        upperTerminalDepth (sourceUpperLogRadius (Real.log R)))) atTop (𝓝 0) := by
  refine ⟨source_upper_quarter_root_internal.comp Real.tendsto_log_atTop,
    source_upper_depth_square_internal.comp Real.tendsto_log_atTop, ?_,
    source_upper_mesh_exponential_internal.comp Real.tendsto_log_atTop, ?_⟩
  · have hh := (source_upper_depth_log_power_internal 1).comp Real.tendsto_log_atTop
    simpa only [Function.comp_def, pow_one] using hh
  · intro c hc
    have hh := (source_upper_depth_exponential_internal c hc).comp Real.tendsto_log_atTop
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simp only [Function.comp_def, Real.exp_log hR]

end SRWTightness
