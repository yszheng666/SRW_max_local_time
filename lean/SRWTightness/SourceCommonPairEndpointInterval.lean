import SRWTightness.SourceCommonPairEndpointPositive
import SRWTightness.SourceCommonPairEndpointErrorLimit

open Filter

namespace SRWTightness

/-- A fixed remaining-time margin guarantees the entire optimized endpoint interval uniformly. -/
theorem source_common_pair_endpoint_interval :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ t →
      6 ≤ sourceTotalTime t - (j : ℝ) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      0 < sourceCommonPairEndpoint t j ∧ 0 < sourceCommonPairScaledEndpoint t j ∧
        sourceCommonPairScaledEndpoint t j < sourceTerminalHeight t := by
  filter_upwards [sourceBarrierSlope_eventually_ge_one,
    source_common_pair_endpoint_error_uniform 1 (by norm_num),
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hθ herr ht
  intro j hj hjt hd hdepth
  have hjT : (j : ℝ) ≤ sourceTotalTime t := by linarith
  have hq := sourceCommonPairEndpoint_ge_four t j hθ hj hjT
  have hq0 : 0 < sourceCommonPairEndpoint t j := by linarith
  have he := (abs_lt.mp (herr j hjt hjT hq0.le hdepth)).2
  have hT : sourceTotalTime t ≠ 0 := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hgap := source_common_pair_endpoint_gap_lower t j hθ hjT hT
  have hm := ((sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1).trans
    (sourceCommonPairInnerRadius_ge_lower t j hdepth)
  exact ⟨hq0, sourceCommonPairScaledEndpoint_pos t j hm hq0, by linarith⟩

end SRWTightness
