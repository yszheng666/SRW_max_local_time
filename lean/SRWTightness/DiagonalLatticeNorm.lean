import SRWTightness.Geometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace SRWTightness

/-- Squared Euclidean distance on the positive lattice diagonal. -/
theorem diagonal_lattice_normSq (n : ℕ) :
    normSq ((n : ℤ), (n : ℤ)) = 2 * (n : ℝ) ^ 2 := by
  simp only [normSq, Int.cast_natCast]
  ring

/-- Euclidean distance on the positive lattice diagonal. -/
theorem diagonal_lattice_norm (n : ℕ) :
    Real.sqrt (normSq ((n : ℤ), (n : ℤ))) = Real.sqrt 2 * (n : ℝ) := by
  rw [diagonal_lattice_normSq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]

/-- The diagonal logarithmic radius includes exactly one half of log two. -/
theorem diagonal_lattice_log_norm (n : ℕ) (hn : 0 < n) :
    Real.log (Real.sqrt (normSq ((n : ℤ), (n : ℤ)))) = Real.log n + Real.log 2 / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [diagonal_lattice_norm,
    Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))) hn0,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end SRWTightness
