import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- The exact completion of the square used in manuscript equation (4.16). -/
theorem source_upper_barrier_square_identity (θ j U K : ℝ) (hden : j + K ≠ 0) :
    (θ * j + U) ^ 2 / (2 * (j + K)) =
      θ ^ 2 * j / 2 + θ * U - θ ^ 2 * K / 2 +
        (U - θ * K) ^ 2 / (2 * (j + K)) := by
  field_simp
  <;> ring

/-- Dropping the nonnegative square preserves the sharp linear height cost. -/
theorem source_upper_barrier_square_lower (θ j U K : ℝ) (hden : 0 < j + K) :
    θ ^ 2 * j / 2 + θ * U - θ ^ 2 * K / 2 ≤
      (θ * j + U) ^ 2 / (2 * (j + K)) := by
  rw [source_upper_barrier_square_identity θ j U K hden.ne']
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by positivity))

/-- The spatial exponential factor separates into a slope error and the source height decay. -/
theorem source_upper_barrier_exponential (θ j U K : ℝ) (hden : 0 < j + K)
    (hθ : 3 / 2 ≤ θ) (hθthree : θ ≤ 3) (hU : 0 ≤ U) (hK : 0 ≤ K) :
    Real.exp (2 * j - (θ * j + U) ^ 2 / (2 * (j + K))) ≤
      Real.exp (9 * K / 2) * Real.exp ((2 - θ ^ 2 / 2) * j) *
        Real.exp (-3 * U / 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := source_upper_barrier_square_lower θ j U K hden
  have hsq : θ ^ 2 ≤ 9 := by nlinarith
  have hcost := mul_le_mul_of_nonneg_right hsq hK
  have hheight := mul_le_mul_of_nonneg_right hθ hU
  nlinarith

end SRWTightness
