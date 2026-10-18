import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace SRWTightness

/-- The exact positive-population mixture of a geometric GW generation simplifies in closed form. -/
theorem geometric_gw_marginal_positive_series (j m : ℕ) (hm : 1 ≤ m) :
    (∑' n : ℕ, (1 / ((j : ℝ) + 1) ^ 2) *
      ((j : ℝ) / ((j : ℝ) + 1)) ^ n * ((m + n).choose m : ℝ) *
        (1 / 2 : ℝ) ^ (m + n + 1)) =
      (1 / ((j : ℝ) + 2) ^ 2) * (((j : ℝ) + 1) / ((j : ℝ) + 2)) ^ (m - 1) := by
  let a : ℝ := (j : ℝ) / ((j : ℝ) + 1)
  let C : ℝ := (1 / ((j : ℝ) + 1) ^ 2) * (1 / 2 : ℝ) ^ (m + 1)
  have h1 : 0 < (j : ℝ) + 1 := by positivity
  have h2 : 0 < (j : ℝ) + 2 := by positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := (div_lt_one h1).mpr (by linarith)
  have hr : ‖a * (1 / 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hterm (n : ℕ) :
      (1 / ((j : ℝ) + 1) ^ 2) * a ^ n * ((m + n).choose m : ℝ) *
        (1 / 2 : ℝ) ^ (m + n + 1) =
      C * (((n + m).choose m : ℝ) * (a * (1 / 2 : ℝ)) ^ n) := by
    rw [show m + n + 1 = (m + 1) + n by omega, pow_add, mul_pow]
    dsimp [C]
    rw [Nat.add_comm n m]
    ring
  have hR : 1 - a * (1 / 2 : ℝ) = ((j : ℝ) + 2) / (2 * ((j : ℝ) + 1)) := by
    dsimp [a]
    field_simp
    ring
  have hratio : (1 / 2 : ℝ) / (1 - a * (1 / 2 : ℝ)) =
      ((j : ℝ) + 1) / ((j : ℝ) + 2) := by
    rw [hR]
    field_simp <;> ring
  have hC : (1 / ((j : ℝ) + 1) ^ 2) *
      (((j : ℝ) + 1) / ((j : ℝ) + 2)) ^ 2 = 1 / ((j : ℝ) + 2) ^ 2 := by
    field_simp <;> ring
  have he : m + 1 = (m - 1) + 2 := by omega
  calc
    _ = ∑' n : ℕ, C * (((n + m).choose m : ℝ) * (a * (1 / 2 : ℝ)) ^ n) :=
      tsum_congr hterm
    _ = C * (1 / (1 - a * (1 / 2 : ℝ)) ^ (m + 1)) := by
      rw [tsum_mul_left, tsum_choose_mul_geometric_of_norm_lt_one m hr]
    _ = (1 / ((j : ℝ) + 1) ^ 2) *
        ((1 / 2 : ℝ) / (1 - a * (1 / 2 : ℝ))) ^ (m + 1) := by
      dsimp [C]
      rw [div_pow (1 / 2 : ℝ) (1 - a * (1 / 2 : ℝ)) (m + 1)]
      ring
    _ = (1 / ((j : ℝ) + 1) ^ 2) *
        (((j : ℝ) + 1) / ((j : ℝ) + 2)) ^ (m + 1) := by rw [hratio]
    _ = ((1 / ((j : ℝ) + 1) ^ 2) *
        (((j : ℝ) + 1) / ((j : ℝ) + 2)) ^ 2) *
          (((j : ℝ) + 1) / ((j : ℝ) + 2)) ^ (m - 1) := by rw [he, pow_add]; ring
    _ = _ := by rw [hC]

end SRWTightness
