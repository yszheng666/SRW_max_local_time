import SRWTightness.SourceUpperRootDepthCost
import SRWTightness.SourceUpperBarrierSlopeFactor

open Filter

namespace SRWTightness

/-- Source (4.31) at every actual selected block, with its slope condition discharged internally. -/
theorem source_upper_actual_root_depth_cost (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      let k := sourceUpperBlockRoot t b
      9 * (k : ℝ) / 8 ≤
        sourceUpperTarget t s ^ 2 / (2 * (sourceUpperCoarseDepth t - k : ℕ)) -
          sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) := by
  filter_upwards [source_upper_branching_depth_bounds, source_upper_barrier_slope_bounds hScale]
    with t hd hslope
  intro b hb s hs hslog
  exact source_upper_root_depth_cost_lower t s (sourceUpperBlockRoot t b)
    (hd b hb).1 (hslope s hs hslog).1

/-- The actual root depth yields the exponential damping required by the spatial sum. -/
theorem source_upper_actual_root_depth_exponential (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      let k := sourceUpperBlockRoot t b
      Real.exp (-(sourceUpperTarget t s ^ 2 /
        (2 * (sourceUpperCoarseDepth t - k : ℕ)))) ≤
        Real.exp (-(sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t))) *
          Real.exp (-(9 * (k : ℝ) / 8)) := by
  filter_upwards [source_upper_actual_root_depth_cost hScale] with t ht
  intro b hb s hs hslog
  dsimp only
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [ht b hb s hs hslog]

end SRWTightness
