import SRWTightness.StoppedUniformTimeGrid
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace SRWTightness

/-- A positive-length stopped grid contains its right endpoint exactly. -/
theorem stoppedUniformTimeGrid_endpoint (a b : ℝ) (N : ℕ) (hN : 0 < N) :
    stoppedUniformTimeGrid a b N N = b := by
  rw [stoppedUniformTimeGrid_of_le a b N N le_rfl]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  <;> ring

/-- Doubling the subdivision count preserves each old grid point at its doubled index. -/
theorem stoppedUniformTimeGrid_double (a b : ℝ) (N k : ℕ) (hk : k ≤ N) :
    stoppedUniformTimeGrid a b (2 * N) (2 * k) = stoppedUniformTimeGrid a b N k := by
  rw [stoppedUniformTimeGrid_of_le a b (2 * N) (2 * k) (Nat.mul_le_mul_left 2 hk),
    stoppedUniformTimeGrid_of_le a b N k hk]
  push_cast
  ring

end SRWTightness
