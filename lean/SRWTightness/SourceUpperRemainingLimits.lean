import SRWTightness.SourceUpperDepthInternal

open Filter
open scoped Topology
namespace SRWTightness

/-- The actual Green reference depth is eventually strictly positive. -/
theorem source_upper_depth_positive_internal :
    ∀ᶠ t : ℝ in atTop, 0 < upperTerminalDepth (sourceUpperLogRadius t) := by
  let B : ℝ := diskGreenEnergyConstant / (2 / Real.pi) + 2
  filter_upwards [source_upper_terminal_depth_internal,
    sourceUpperLogRadius_eventually (B + 1)] with t hd ht
  have hh := (abs_le.mp hd).1
  dsimp [B] at ht
  linarith

/-- The original outer-area exponential in (4.3) vanishes for every positive coefficient. -/
theorem source_upper_depth_exponential_internal (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ ↦ (Real.exp t) ^ 2 *
      Real.exp (-c * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t))) atTop (𝓝 0) := by
  have hratio : Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) / t)
      atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using source_upper_depth_log_power_internal 0
  have hs := hratio.eventually (eventually_lt_nhds (show (0 : ℝ) < c / 3 by positivity))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t ↦ by positivity)) ?_
    Real.tendsto_exp_neg_atTop_nhds_zero
  filter_upwards [hs, source_upper_depth_positive_internal,
    eventually_gt_atTop (0 : ℝ)] with t ht hd ht0
  have hdt := (div_lt_iff₀ ht0).mp ht
  have hq : 3 * t ≤ c * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right hdt.le (show 0 ≤ 3 * t by positivity)]
  have he : (Real.exp t) ^ 2 *
      Real.exp (-c * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) =
      Real.exp (2 * t - c * t ^ 2 / upperTerminalDepth (sourceUpperLogRadius t)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact Real.exp_le_exp.mpr (by linarith)

end SRWTightness
