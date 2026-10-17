import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace SRWTightness

/-- A unit shift in a positive Gaussian deficit retains half its original quadratic decay. -/
theorem positive_square_unit_shift (q : ℝ) :
    (max q 0) ^ 2 / 2 - 1 ≤ (max (q - 1) 0) ^ 2 := by
  by_cases hq : q ≤ 0
  · rw [max_eq_right hq]
    nlinarith [sq_nonneg (max (q - 1) 0)]
  · have hq0 : 0 ≤ q := (lt_of_not_ge hq).le
    rw [max_eq_left hq0]
    by_cases hq1 : q ≤ 1
    · rw [max_eq_right (by linarith : q - 1 ≤ 0)]
      nlinarith
    · rw [max_eq_left (by linarith : 0 ≤ q - 1)]
      nlinarith [sq_nonneg (q - 2)]

/-- The full unit-window exponential is bounded by the original positive-deficit Gaussian shape. -/
theorem positive_gaussian_unit_shift_bound (q κ d : ℝ) (hκ : 0 ≤ κ) (hd : 1 ≤ d) :
    Real.exp (-2 * q + 2 - κ * (max (q - 1) 0) ^ 2 / d) ≤
      Real.exp (2 + κ) * Real.exp (-2 * q - (κ / 2) * (max q 0) ^ 2 / d) := by
  have hd0 : 0 < d := by linarith
  have hshift := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (positive_square_unit_shift q) hκ) hd0.le
  have hscale : κ / d ≤ κ := div_le_self hκ hd
  have he : -2 * q + 2 - κ * (max (q - 1) 0) ^ 2 / d ≤
      (2 + κ) + (-2 * q - (κ / 2) * (max q 0) ^ 2 / d) := by
    have hr : κ * ((max q 0) ^ 2 / 2 - 1) / d =
        (κ / 2) * (max q 0) ^ 2 / d - κ / d := by ring
    rw [hr] at hshift
    linarith
  exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_add _ _)

end SRWTightness
