import SRWTightness.SourceUpperDepthEventually

open Filter
open scoped Topology

namespace SRWTightness

/-- The coarse depth is between half the logarithmic radius and the logarithmic radius eventually. -/
theorem source_upper_coarse_linear_depth :
    ∀ᶠ t : ℝ in atTop, t / 2 ≤ (sourceUpperCoarseDepth t : ℝ) ∧
      (sourceUpperCoarseDepth t : ℝ) ≤ t := by
  filter_upwards [source_upper_coarse_range_eventually,
    sourceUpperLogRadius_div_tendsto.eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    eventually_ge_atTop (max 1 (4 * (Real.log 32 + 2)))] with t hc hs ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  have htC := (le_max_right _ _).trans ht
  have hD := (div_lt_iff₀ ht0).mp hs
  have hh := source_upper_coarse_depth_error t hc
  have hD0 : 0 ≤ sourceUpperLogRadius t := by unfold sourceUpperLogRadius; positivity
  have hlog : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  constructor <;> linarith

end SRWTightness
