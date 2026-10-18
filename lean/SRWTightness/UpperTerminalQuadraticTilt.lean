import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace SRWTightness

/-- A linear terminal-window tilt is absorbed into Gaussian decay with an explicit quadratic cost. -/
theorem upper_terminal_quadratic_tilt (d c β q : ℝ) (hd : 0 < d) (hc : 0 < c) :
    β * q - c * q ^ 2 / d ≤ d * β ^ 2 / c - 3 * c * q ^ 2 / (4 * d) := by
  have hs : 0 ≤ (d * β - c * q / 2) ^ 2 / (d * c) :=
    div_nonneg (sq_nonneg _) (mul_pos hd hc).le
  have he : d * β ^ 2 / c + c * q ^ 2 / (4 * d) - β * q =
      (d * β - c * q / 2) ^ 2 / (d * c) := by
    field_simp [hd.ne', hc.ne'] <;> ring
  rw [← he] at hs
  have hi : c * q ^ 2 / d = 4 * (c * q ^ 2 / (4 * d)) := by ring
  have hj : 3 * c * q ^ 2 / (4 * d) = 3 * (c * q ^ 2 / (4 * d)) := by ring
  rw [hi, hj]
  linarith

/-- Unit-window rounding preserves at least half the positive Gaussian quadratic cost. -/
theorem upper_terminal_rounded_square (q : ℝ) :
    (max q 0) ^ 2 ≤ 2 * (max (q - 1) 0) ^ 2 + 2 := by
  by_cases hq : 1 ≤ q
  · rw [max_eq_left (by linarith : 0 ≤ q), max_eq_left (by linarith : 0 ≤ q - 1)]
    nlinarith [sq_nonneg (q - 2)]
  · rw [max_eq_right (by linarith : q - 1 ≤ 0)]
    by_cases h : 0 ≤ q
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right (by linarith : q ≤ 0)]
      norm_num

end SRWTightness
