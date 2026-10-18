import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- Spatial counting cancels the common quadratic exponent with exactly the source power t^26. -/
theorem common_spatial_cancellation (t j J w E : ℝ) (ht : 0 < t)
    (hJ : J ≤ 10 * Real.log t + 6) :
    Real.exp (4 * t - 2 * j - 2 * J) *
      (t ^ 2 * Real.exp (-4 * t + 2 * j - 2 * w + 4 * Real.log t + 4 * J + E)) ≤
      Real.exp (E + 12) * t ^ 26 * Real.exp (-2 * w) := by
  have hexp := Real.exp_le_exp.mpr
    (show 4 * Real.log t + 2 * J + E ≤ 24 * Real.log t + E + 12 by linarith)
  have he24 : Real.exp (24 * Real.log t) = t ^ 24 := by
    rw [show (24 : ℝ) = (24 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log ht]
  calc
    _ = t ^ 2 * Real.exp (-2 * w) * Real.exp (4 * Real.log t + 2 * J + E) := by
      rw [mul_comm (Real.exp (4 * t - 2 * j - 2 * J)), mul_assoc, ← Real.exp_add,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ t ^ 2 * Real.exp (-2 * w) * Real.exp (24 * Real.log t + E + 12) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (E + 12) * t ^ 26 * Real.exp (-2 * w) := by
      rw [show 24 * Real.log t + E + 12 = 24 * Real.log t + (E + 12) by ring,
        Real.exp_add, he24]
      ring

end SRWTightness
