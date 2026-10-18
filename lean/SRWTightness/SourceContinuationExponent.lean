import SRWTightness.SourceContinuationRange
import SRWTightness.ContinuationExponentIdentity

open Filter
namespace SRWTightness

/-- Equation (7.32) with the source slope and generation, throughout its early range. -/
theorem source_continuation_exponent_identity :
    ∀ᶠ t : ℝ in atTop, ∀ (ν : ℕ) (x : ℝ), ν ≤ 2 * sourceCoarseLowerLevel t →
      (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
          (2 * ((sourceCoarseGeneration t : ℝ) - ν)) =
        sourceBarrierSlope t ^ 2 * (sourceCoarseGeneration t : ℝ) / 2 +
          sourceBarrierSlope t ^ 2 * ν / 2 - sourceBarrierSlope t * x +
          (sourceBarrierSlope t * ν - x) ^ 2 /
            (2 * ((sourceCoarseGeneration t : ℝ) - ν)) := by
  filter_upwards [source_continuation_remaining_time, eventually_gt_atTop (0 : ℝ)]
    with t ht ht0
  intro ν x hν
  exact continuation_exponent_identity _ _ _ _ (ne_of_gt (by linarith [ht ν hν]))

end SRWTightness
