import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace SRWTightness

/-- The diagonal cosine numerator is a finite odd-sine sum times the sine denominator. -/
theorem diagonal_trigonometric_sum (n : ℕ) (u : ℝ) :
    1 - Real.cos (2 * (n : ℝ) * u) =
      (2 * ∑ j ∈ Finset.range n, Real.sin ((2 * (j : ℝ) + 1) * u)) * Real.sin u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := Real.two_mul_sin_mul_sin ((2 * (n : ℝ) + 1) * u) u
    have hminus : (2 * (n : ℝ) + 1) * u - u = 2 * (n : ℝ) * u := by ring
    have hplus : (2 * (n : ℝ) + 1) * u + u = 2 * ((n : ℝ) + 1) * u := by ring
    rw [hminus, hplus] at ht
    simp only [Nat.cast_add, Nat.cast_one, Finset.sum_range_succ]
    nlinarith

/-- Every positive odd sine frequency has its exact half-circle integral. -/
theorem odd_sine_integral (j : ℕ) :
    (∫ u in 0..Real.pi, Real.sin ((2 * (j : ℝ) + 1) * u)) = 2 / (2 * j + 1) := by
  rw [intervalIntegral.integral_comp_mul_left Real.sin (by positivity : (2 * (j : ℝ) + 1) ≠ 0),
    mul_zero, integral_sin, Real.cos_zero]
  have hc : Real.cos ((2 * (j : ℝ) + 1) * Real.pi) = -1 := by
    have hh := Real.cos_nat_mul_pi (2 * j + 1)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul] using hh
  rw [hc]
  simp only [smul_eq_mul]
  ring

end SRWTightness
