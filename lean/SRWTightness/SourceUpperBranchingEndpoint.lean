import SRWTightness.SourceUpperBranchingBarrier
import SRWTightness.SourceUpperBranchingDepth
import SRWTightness.SourceUpperSlopeError

open Filter
open scoped Topology

namespace SRWTightness

/-- The source branching endpoint is eventually at most three times logarithmic radius. -/
theorem source_upper_branching_endpoint_bound (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      sourceUpperBranchingEnd t s ≤ 3 * t := by
  obtain ⟨B, _, hc⟩ := source_upper_threshold_conditions hScale
  have hlog : Tendsto (fun t : ℝ ↦ (1 + Real.sqrt Real.pi) * (Real.log t / t))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [hc, hlog.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    (source_upper_depth_log_power_limit hScale 0).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_ge_atTop (16 : ℝ)] with t ht hl hd ht16
  intro s hs hslog
  have hy := source_upper_height_bounds t s ht.1 hs hslog
  have hT : 0 < sourceUpperTotalDepth t := by linarith [ht.2.2.2.1]
  have hd1 := ht.2.2.2.2.2.2.1
  have hθ : 0 ≤ sourceUpperSlope t s := div_nonneg (by linarith [hy.1]) hT.le
  have hx : sourceUpperTarget t s ≤ sourceUpperHeight t s := by
    have hh : sourceUpperSlope t s * sourceUpperTotalDepth t = sourceUpperHeight t s :=
      div_mul_cancel₀ _ hT.ne'
    unfold sourceUpperTarget
    unfold sourceUpperTotalDepth at hh
    nlinarith [mul_nonneg hθ (show 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) by linarith)]
  have hp := Real.rpow_le_self_of_one_le hd1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  simp only [pow_zero, mul_one] at hd
  have hd' := (div_lt_iff₀ ht.1).mp hd
  have hl' : (1 + Real.sqrt Real.pi) * Real.log t < t / 4 := by
    have hh : (1 + Real.sqrt Real.pi) * Real.log t / t < 1 / 4 := by
      simpa only [mul_div_assoc] using hl
    have := (div_lt_iff₀ ht.1).mp hh
    linarith
  unfold sourceUpperBranchingEnd
  nlinarith [hy.2]

end SRWTightness
