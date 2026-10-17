import SRWTightness.SourceUpperTerminalTiltLimit
import SRWTightness.SourceUpperBarrierSlopeFactor

open Filter
open scoped Topology

namespace SRWTightness

/-- The actual terminal tilt has arbitrarily small squared cost, uniformly in height and block. -/
theorem source_upper_terminal_tilt_uniform (hScale : ExponentialFloorScaleInput)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      upperTerminalDepth (sourceUpperLogRadius t) *
        (sourceUpperTarget t s /
          (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) - 2) ^ 2 ≤ ε := by
  obtain ⟨B, hB, hc⟩ := source_upper_threshold_conditions hScale
  filter_upwards [hc, source_upper_block_root_conditions, source_upper_branching_depth_bounds,
    source_upper_barrier_slope_bounds hScale,
    (source_upper_terminal_tilt_square_limit hScale B).eventually
      (eventually_lt_nhds hε)] with t ht hk hd hθ hsmall
  intro b hb s hs hslog
  have hL : t / 2 ≤ (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) := by
    linarith [(hd b hb).2.1]
  have hθ0 : 0 ≤ sourceUpperSlope t s := by linarith [(hθ s hs hslog).1]
  have he := source_upper_terminal_tilt_error t s B b ht.1 hB hs hslog
    ht.2.2.2.1 ht.2.2.2.2.1 (hd b hb).1 (hk b hb).2.1 hL hθ0 (hθ s hs hslog).2
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    linarith [ht.2.2.2.2.2.2.1]
  have hsq := mul_self_le_mul_self (abs_nonneg _) he
  rw [← sq, sq_abs, ← sq] at hsq
  exact (mul_le_mul_of_nonneg_left hsq hd0).trans hsmall.le

end SRWTightness
