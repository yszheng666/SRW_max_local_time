import SRWTightness.LatticeSquare
import Mathlib.Data.Nat.Log

namespace SRWTightness

/-- Enlarging an integer square to the next dyadic square multiplies its side by at most two. -/
theorem lattice_square_dyadic_cover (N : ℕ) (hN : 4 ≤ N) :
    ∃ n : ℕ, 2 ≤ n ∧ N ≤ 2 ^ n ∧ 2 ^ n ≤ 2 * N ∧
      ∀ a : Site, latticeSquareInterior a N ⊆ latticeSquareInterior a (2 ^ n) := by
  let n := Nat.log 2 N + 1
  have hn : 2 ≤ n := by
    have hh := Nat.log_pos (by norm_num : 1 < (2 : ℕ)) (show 2 ≤ N by omega)
    dsimp [n]
    omega
  have hp : N < 2 ^ n := Nat.lt_pow_of_log_lt (by norm_num) (by dsimp [n]; omega)
  have hu : 2 ^ n ≤ 2 * N := by
    have hh := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
    dsimp [n]
    rw [pow_succ]
    omega
  refine ⟨n, hn, hp.le, hu, ?_⟩
  intro a x hx
  have hs : (N : ℤ) ≤ (2 ^ n : ℕ) := by exact_mod_cast hp.le
  rw [mem_latticeSquareInterior] at hx ⊢
  omega

end SRWTightness
