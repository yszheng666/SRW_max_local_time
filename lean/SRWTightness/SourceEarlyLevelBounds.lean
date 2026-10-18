import SRWTightness.SourceContinuationRange
import SRWTightness.SourceRootGWHorizon

open Filter
namespace SRWTightness

/-- Every early level is within the actual root depth, the physical time and the barrier time. -/
theorem source_early_level_bounds :
    ∀ᶠ t : ℝ in atTop, 2 ≤ t ∧ ∀ j : ℕ, j ≤ 2 * sourceCoarseLowerLevel t →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) ∧
      (j : ℝ) ≤ t ∧ (j : ℝ) ≤ sourceTotalTime t := by
  filter_upwards [source_continuation_cutoff_reserve, source_deficit_large_conditions,
    source_continuation_remaining_time, source_root_gw_horizon_large]
    with t hreserve ht htime hN
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  refine ⟨ht2, ?_⟩
  intro j hj
  have hjr : (j : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by exact_mod_cast hj
  have hjt : (j : ℝ) ≤ t := by linarith [ht.2.2.1]
  have hnreal : (j : ℝ) ≤
      ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime j hj]
  have hn : j ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by
    exact_mod_cast hnreal
  have hdepth : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  refine ⟨hdepth, hjt, ?_⟩
  have hN0 : 0 ≤ (sourceCoarseGeneration t : ℝ) := by rw [← hN.2]; positivity
  unfold sourceTotalTime
  linarith

end SRWTightness
