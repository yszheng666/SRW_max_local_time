import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Inverse signed-tilt weight on each pair excess/deficit window. -/
theorem pair_inverse_tilt_window (Λ F G S At d v q f n m l C ε : ℝ)
    (hΛ : Λ ≤ 4 * d - 2 * v + C) (hAt : 2 * d + q - ε ≤ At)
    (hF : At + n ≤ F) (hG : At + m ≤ G)
    (hS : S ≤ 2 * v + q - f - l) :
    Real.exp (Λ - (2 * F + 2 * G - 2 * S)) ≤
      Real.exp (C + 4 * ε) * Real.exp (-2 * d - 2 * (d - v) - 2 * q - 2 * f) *
        Real.exp (-2 * (n + m + l)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Nonnegative window indices produce the three geometric inverse-tilt factors. -/
theorem pair_inverse_tilt_window_nat (Λ F G S At d v q f C ε : ℝ) (n m l : ℕ)
    (hΛ : Λ ≤ 4 * d - 2 * v + C) (hAt : 2 * d + q - ε ≤ At)
    (hF : At + n ≤ F) (hG : At + m ≤ G)
    (hS : S ≤ 2 * v + q - f - l) :
    Real.exp (Λ - (2 * F + 2 * G - 2 * S)) ≤
      Real.exp (C + 4 * ε) * Real.exp (-2 * d - 2 * (d - v) - 2 * q - 2 * f) *
        ((Real.exp (-2)) ^ n * (Real.exp (-2)) ^ m * (Real.exp (-2)) ^ l) := by
  have hh := pair_inverse_tilt_window Λ F G S At d v q f n m l C ε hΛ hAt hF hG hS
  have he : Real.exp (-2 * ((n : ℝ) + m + l)) =
      (Real.exp (-2)) ^ n * (Real.exp (-2)) ^ m * (Real.exp (-2)) ^ l := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hh
  exact hh

end SRWTightness
