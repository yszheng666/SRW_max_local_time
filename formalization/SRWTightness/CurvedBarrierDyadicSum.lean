import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- One dyadic crossing cost, with the source boundary bounded by (3L)^γ. -/
theorem curvedBarrier_dyadic_cost (H γ : ℝ) (hH : 0 < H) (j : ℕ) :
    (3 * ((2 : ℝ) ^ j * H)) ^ γ / Real.sqrt ((2 : ℝ) ^ j * H) =
      (3 : ℝ) ^ γ * H ^ (γ - 1 / 2) * ((2 : ℝ) ^ (γ - 1 / 2)) ^ j := by
  have hL : 0 < (2 : ℝ) ^ j * H := by positivity
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hL.le, Real.sqrt_eq_rpow,
    mul_div_assoc, ← Real.rpow_sub hL, Real.mul_rpow (by positivity) hH.le,
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (j : ℝ),
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Uniform control of all dyadic crossing costs when γ is below one half. -/
theorem curvedBarrier_dyadic_sum (H γ : ℝ) (hH : 0 < H) (hγ : γ < 1 / 2) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      (3 * ((2 : ℝ) ^ j * H)) ^ γ / Real.sqrt ((2 : ℝ) ^ j * H)) ≤
      ((3 : ℝ) ^ γ * H ^ (γ - 1 / 2)) / (1 - (2 : ℝ) ^ (γ - 1 / 2)) := by
  simp_rw [curvedBarrier_dyadic_cost H γ hH]
  rw [← Finset.mul_sum]
  have hr : (2 : ℝ) ^ (γ - 1 / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum := geom_sum_Ico_le_of_lt_one
    (m := 0) (n := n) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hr
  simp only [Nat.Ico_zero_eq_range, pow_zero] at hsum
  have h := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (3 : ℝ) ^ γ * H ^ (γ - 1 / 2))
  simpa only [mul_one_div] using h

/-- The initial interval and n dyadic intervals cover [0,2^n H]. -/
theorem curvedBarrier_dyadic_cover (H t : ℝ) (n : ℕ)
    (ht : t ≤ (2 : ℝ) ^ n * H) :
    t ≤ H ∨ ∃ j < n, (2 : ℝ) ^ j * H ≤ t ∧ t ≤ 2 * ((2 : ℝ) ^ j * H) := by
  induction n with
  | zero => simpa using ht
  | succ n ih =>
    by_cases h : t ≤ (2 : ℝ) ^ n * H
    · rcases ih h with h0 | ⟨j, hj, hlo, hhi⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hlo, hhi⟩
    · right
      refine ⟨n, Nat.lt_succ_self n, (lt_of_not_ge h).le, ?_⟩
      calc t ≤ (2 : ℝ) ^ (n + 1) * H := ht
           _ = 2 * ((2 : ℝ) ^ n * H) := by rw [pow_succ]; ring

end SRWTightness
