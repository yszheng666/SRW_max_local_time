import SRWTightness.SourceUpperBlockRootGeometry
import SRWTightness.LogPowerDomination

open Filter
open scoped Topology

namespace SRWTightness

/-- Every actual selected root lies within the source coarse range for all sufficiently large t. -/
theorem source_upper_block_root_coarse_range :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      sourceUpperBlockRoot t b ≤ sourceUpperCoarseDepth t := by
  have hsmall := sourceUpperLogRadius_div_tendsto.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlog := affine_log_eventually_le_rpow 1 (Real.log 32 + 3) (1 / 2) 1
    (by norm_num) (by norm_num)
  filter_upwards [source_upper_block_root_conditions, source_upper_coarse_range_eventually,
    hsmall, hlog, eventually_gt_atTop (0 : ℝ)] with t hr hc hd hl ht0
  intro b hb
  have hk := (hr b hb).2.1
  have hD := (div_lt_iff₀ ht0).mp hd
  have hN := (source_upper_coarse_depth_error t hc).1
  simp only [one_mul, Real.rpow_one] at hl
  have h : (sourceUpperBlockRoot t b : ℝ) ≤ (sourceUpperCoarseDepth t : ℝ) := by linarith
  exact_mod_cast h

end SRWTightness
