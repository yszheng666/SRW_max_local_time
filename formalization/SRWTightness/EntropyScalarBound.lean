import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The real relative-entropy integrand is nonnegative, including at zero. -/
theorem entropy_integrand_nonnegative (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ x * Real.log x - x + 1 := by
  by_cases hzero : x = 0
  · subst x; norm_num
  have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hx
  rw [mul_sub, mul_one, mul_inv_cancel₀ hzero] at hh
  linarith

/-- Squared square-root distance is bounded by the relative-entropy integrand. -/
theorem sqrt_distance_le_entropy (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt x - 1) ^ 2 ≤ x * Real.log x - x + 1 := by
  have h := entropy_integrand_nonnegative (Real.sqrt x) (Real.sqrt_nonneg x)
  rw [Real.log_sqrt hx] at h
  have hm := mul_nonneg (show 0 ≤ 2 * Real.sqrt x by positivity) h
  have hs := Real.sq_sqrt hx
  have hslog := congrArg (fun y : ℝ ↦ y * Real.log x) hs
  nlinarith

/-- A tunable pointwise entropy estimate that can be integrated without a density lower bound. -/
theorem entropy_absolute_error_parameter (x q : ℝ) (hx : 0 ≤ x) (hq : 0 ≤ q) :
    2 * q * |x - 1| ≤ (x * Real.log x - x + 1) + 2 * q ^ 2 * (x + 1) := by
  have hs := Real.sq_sqrt hx
  have hr := Real.sqrt_nonneg x
  have he : |x - 1| = |Real.sqrt x - 1| * (Real.sqrt x + 1) := by
    rw [← abs_of_nonneg (show 0 ≤ Real.sqrt x + 1 by positivity), ← abs_mul]
    congr 1
    nlinarith
  have h := sqrt_distance_le_entropy x hx
  have hp := sq_nonneg (|Real.sqrt x - 1| - q * (Real.sqrt x + 1))
  have ha := sq_abs (Real.sqrt x - 1)
  have hsum : (Real.sqrt x + 1) ^ 2 ≤ 2 * (x + 1) := by
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg q)
  rw [he]
  nlinarith

end SRWTightness
