import SRWTightness.SourceUpperBranchingEndpoint

open Filter
open scoped Topology

namespace SRWTightness

/-- An explicit upper error for the endpoint slope at any actual selected block. -/
noncomputable def sourceUpperRootSlopeError (t B : ℝ) : ℝ :=
  ((10 + 2 * Real.sqrt Real.pi) * Real.log t + 4 * B + 14 +
    4 * upperTerminalDepth (sourceUpperLogRadius t)) / t

/-- The endpoint slope error vanishes even after multiplication by the logarithmic root scale. -/
theorem source_upper_root_slope_error_limit (hScale : ExponentialFloorScaleInput) (B K : ℝ) :
    Tendsto (fun t : ℝ ↦ sourceUpperRootSlopeError t B * (Real.log t + 1 + K))
      atTop (𝓝 0) := by
  have h0 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero
  have hd0 := source_upper_depth_log_power_limit hScale 0
  have hd1 := source_upper_depth_log_power_limit hScale 1
  have hi : Tendsto (fun t : ℝ ↦ 1 / t) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0))
  have hh := (h1.const_mul (10 + 2 * Real.sqrt Real.pi)).add
    ((h0.const_mul ((10 + 2 * Real.sqrt Real.pi) * (1 + K) + 4 * B + 14)).add
      ((hi.const_mul ((4 * B + 14) * (1 + K))).add
        ((hd1.const_mul 4).add (hd0.const_mul (4 * (1 + K))))))
  convert hh using 1
  · funext t
    simp only [sourceUpperRootSlopeError, pow_zero, pow_one, mul_one, id_eq]
    ring
  · simp

end SRWTightness
