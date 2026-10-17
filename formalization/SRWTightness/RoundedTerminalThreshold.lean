import SRWTightness.TerminalThresholdAlgebra
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

theorem terminalThreshold_rounding_bounds (g y : ℝ) (hg : 0 < g) :
    0 ≤ (Nat.ceil (g * y ^ 2 / 2) : ℝ) - g * y ^ 2 / 2 ∧
      (Nat.ceil (g * y ^ 2 / 2) : ℝ) - g * y ^ 2 / 2 ≤ 1 := by
  have h0 := Nat.le_ceil (g * y ^ 2 / 2)
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ g * y ^ 2 / 2 by positivity)
  constructor <;> linarith

theorem terminalThreshold_rounded_error (α g u y : ℝ)
    (hg : 0 < g) (hα : g ≤ α) (hu : 0 < u) :
    |terminalOccupationThreshold (Nat.ceil (g * y ^ 2 / 2)) α g u -
      (y ^ 2 - u ^ 2) / (2 * u)| ≤
      1 / (u * g) + (α - g) * (y ^ 2 + u ^ 2) / (2 * u * g) :=
  terminalThreshold_error_bound _ α g u y hg hα hu
    (terminalThreshold_rounding_bounds g y hg).1 (terminalThreshold_rounding_bounds g y hg).2

theorem terminalThreshold_square_difference (u y : ℝ) (hu : 0 < u) :
    (y ^ 2 - u ^ 2) / (2 * u) = y - u + (y - u) ^ 2 / (2 * u) := by
  field_simp
  <;> ring

/-- The ideal threshold differs from the source target by a quadratic gap and a slope error. -/
theorem terminalThreshold_deficit_identity (u y θ d q : ℝ) (hu : 0 < u)
    (hdef : y - u = θ * d + q) :
    (y ^ 2 - u ^ 2) / (2 * u) - (2 * d + q) =
      (y - u) ^ 2 / (2 * u) + (θ - 2) * d := by
  rw [terminalThreshold_square_difference u y hu]
  nlinarith

/-- Combined rounding, intensity, quadratic-gap and slope errors for the source target. -/
theorem terminalThreshold_deficit_bound (cutoff α g u y θ d q : ℝ)
    (hg : 0 < g) (hα : g ≤ α) (hu : 0 < u)
    (hround : 0 ≤ cutoff - g * y ^ 2 / 2) (hround1 : cutoff - g * y ^ 2 / 2 ≤ 1)
    (hdef : y - u = θ * d + q) :
    |terminalOccupationThreshold cutoff α g u - (2 * d + q)| ≤
      (1 / (u * g) + (α - g) * (y ^ 2 + u ^ 2) / (2 * u * g)) +
        ((y - u) ^ 2 / (2 * u) + |θ - 2| * |d|) := by
  have he := terminalThreshold_error_bound cutoff α g u y hg hα hu hround hround1
  have hs : |(y ^ 2 - u ^ 2) / (2 * u) - (2 * d + q)| ≤
      (y - u) ^ 2 / (2 * u) + |θ - 2| * |d| := by
    rw [terminalThreshold_deficit_identity u y θ d q hu hdef]
    exact (abs_add_le _ _).trans_eq (by
      rw [abs_of_nonneg (by positivity : 0 ≤ (y - u) ^ 2 / (2 * u)), abs_mul])
  exact (abs_sub_le _ _ _).trans (add_le_add he hs)

end SRWTightness
