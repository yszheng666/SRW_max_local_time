import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace SRWTightness

/-- Expanding the terminal quadratic leaves a nonpositive residual after the target tilt. -/
theorem upper_terminal_quadratic_exponent (L x q z : ℝ) (hL : 0 < L) :
    -(x - q) ^ 2 / (2 * L) - 2 * q + z ≤
      -x ^ 2 / (2 * L) + ((x / L - 2) * q + z) := by
  have he : -(x - q) ^ 2 / (2 * L) - 2 * q + z =
      -x ^ 2 / (2 * L) + ((x / L - 2) * q + z) - q ^ 2 / (2 * L) := by
    field_simp
    <;> ring
  rw [he]
  exact sub_le_self _ (div_nonneg (sq_nonneg q) (by positivity))

/-- Terminal quadratic decay factors into the baseline and the exact remaining-depth tilt. -/
theorem upper_terminal_quadratic_factor (L x q z : ℝ) (hL : 0 < L) :
    Real.exp (-(x - q) ^ 2 / (2 * L) - 2 * q + z) ≤
      Real.exp (-x ^ 2 / (2 * L)) * Real.exp ((x / L - 2) * q + z) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (upper_terminal_quadratic_exponent L x q z hL)

end SRWTightness
