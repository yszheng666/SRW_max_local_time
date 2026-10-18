import SRWTightness.SourceUpperDepthEventually

open Filter
open scoped Topology
namespace SRWTightness

/-- Actual terminal Green depth differs from its logarithmic scale by a fixed constant. -/
theorem source_upper_terminal_depth_eventually (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop,
      |upperTerminalDepth (sourceUpperLogRadius t) - sourceUpperLogRadius t| ≤
        diskGreenEnergyConstant / (2 / Real.pi) + 2 := by
  obtain ⟨u₀, _, hs⟩ := hScale 1 (by norm_num)
  filter_upwards [sourceUpperLogRadius_eventually u₀] with t ht
  obtain ⟨hR, _, _, _, hlog, _⟩ := hs (sourceUpperLogRadius t) ht
  exact source_upper_terminal_depth_error _ hR hlog

/-- Every fixed logarithmic weight times the actual terminal depth is negligible against t. -/
theorem source_upper_depth_log_power_limit (hScale : ExponentialFloorScaleInput) (n : ℕ) :
    Tendsto (fun t : ℝ ↦
      upperTerminalDepth (sourceUpperLogRadius t) * (Real.log t) ^ n / t) atTop (𝓝 0) := by
  let B := diskGreenEnergyConstant / (2 / Real.pi) + 2
  have hhigh := (Real.isLittleO_pow_log_id_atTop (n := 4 + n)).tendsto_div_nhds_zero
  have hlow := (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero
  have hlim : Tendsto (fun t : ℝ ↦
      (sourceUpperLogRadius t + B) * (Real.log t) ^ n / t) atTop (𝓝 0) := by
    have hh := (hhigh.const_mul (8 ^ 4 : ℝ)).add (hlow.const_mul B)
    convert hh using 1
    · funext t
      simp only [sourceUpperLogRadius, id_eq, mul_pow, pow_add]
      ring
    · simp
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
      unfold upperTerminalDepth diskGreen
      exact div_nonneg (killedGreen_nonneg _ _ _) (by positivity)
    have hl : 0 ≤ Real.log t := Real.log_nonneg ht
    positivity
  · filter_upwards [source_upper_terminal_depth_eventually hScale,
      eventually_ge_atTop (1 : ℝ)] with t hd ht
    have hup : upperTerminalDepth (sourceUpperLogRadius t) ≤ sourceUpperLogRadius t + B := by
      have hh := (abs_le.mp hd).2
      dsimp [B]
      linarith
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hup (pow_nonneg (Real.log_nonneg ht) n)) (by linarith)

end SRWTightness
