import SRWTightness.SourceCommonPairEndpointLinearError
import SRWTightness.SourceForestErrorDecay

open Filter
open scoped Topology

namespace SRWTightness

/-- The common-endpoint normalization majorant vanishes on the actual source profile. -/
theorem source_common_pair_endpoint_error_majorant_tendsto_zero :
    Tendsto (fun t : ℝ ↦ 56 * (4 + 4 * t) / sourceLowerRadius t) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ ↦ 448 * t ^ 2 / sourceLowerRadius t) atTop (𝓝 0) := by
    have heq : sourceForestQuadraticError 2 0 1 =
        fun t : ℝ ↦ 448 * t ^ 2 / sourceLowerRadius t := by
      funext t
      simp [sourceForestQuadraticError]
      <;> ring
    rw [← heq]
    exact source_forest_quadratic_error_tendsto_zero 2 0 1
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact div_nonneg (by nlinarith) (sourceLowerRadius_pos t).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    apply div_le_div_of_nonneg_right _ (sourceLowerRadius_pos t).le
    nlinarith [sq_nonneg (t - 1)]

/-- The normalized endpoint differs by o(1), uniformly over the allowed positive coarse endpoints. -/
theorem source_common_pair_endpoint_error_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ,
      (j : ℝ) ≤ t → (j : ℝ) ≤ sourceTotalTime t →
      0 ≤ sourceCommonPairEndpoint t j →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      |sourceCommonPairScaledEndpoint t j - sourceCommonPairEndpoint t j| < ε := by
  have he := (tendsto_order.1 source_common_pair_endpoint_error_majorant_tendsto_zero).2 ε hε
  filter_upwards [he, eventually_ge_atTop (sourceScaleThreshold 4),
    eventually_ge_atTop (2 * sourceTotalTimeError)] with t ht hs hT
  intro j hjt hjT hq hdepth
  exact (source_common_pair_endpoint_linear_error t j hs hT hjt hjT hq hdepth).trans_lt ht

end SRWTightness
