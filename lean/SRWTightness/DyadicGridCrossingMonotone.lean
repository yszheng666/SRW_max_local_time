import SRWTightness.StoppedUniformGridNesting
import Mathlib.Order.Monotone.Basic

namespace SRWTightness

/-- Crossing on successive dyadic time grids is an increasing sequence of events. -/
theorem dyadic_grid_crossing_monotone {Ω : Type*} (X : ℝ → Ω → ℝ) (a b q : ℝ) :
    Monotone (fun n : ℕ ↦ {ω | ∃ k ≤ 2 ^ n,
      q ≤ X (stoppedUniformTimeGrid a b (2 ^ n) k) ω}) := by
  apply monotone_nat_of_le_succ
  intro n ω hω
  obtain ⟨k, hk, hcross⟩ := hω
  have hn : 2 ^ (n + 1) = 2 * 2 ^ n := by simp [pow_succ, Nat.mul_comm]
  refine ⟨2 * k, ?_, ?_⟩
  · rw [hn]
    exact Nat.mul_le_mul_left 2 hk
  · rw [hn, stoppedUniformTimeGrid_double a b (2 ^ n) k hk]
    exact hcross

end SRWTightness
