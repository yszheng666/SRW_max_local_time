import SRWTightness.SourceEarlyLevelBounds
import SRWTightness.SourceCommonPairEndpoint

open Filter

namespace SRWTightness

/-- Every early level lies on the increasing side of the original symmetric barrier. -/
theorem source_early_barrier_minimum :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ 2 * sourceCoarseLowerLevel t →
      min (j : ℝ) (sourceTotalTime t - j) = j := by
  filter_upwards [source_continuation_cutoff_reserve, source_deficit_large_conditions]
    with t hc ht
  intro j hj
  have hjr : (j : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by exact_mod_cast hj
  have hT := sourceTotalTime_ge_half t ht.1 ht.2.1
  apply min_eq_left
  linarith [ht.2.2.1, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- The early common endpoint has the exact power deficit used by the joint-root moment. -/
theorem source_early_endpoint_formula :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ 2 * sourceCoarseLowerLevel t →
      sourceCommonPairEndpoint t j =
        4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ) := by
  filter_upwards [source_early_barrier_minimum] with t ht
  intro j hj
  unfold sourceCommonPairEndpoint
  rw [ht j hj]

end SRWTightness
