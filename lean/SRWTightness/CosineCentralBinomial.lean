import SRWTightness.FourierCosineMoments
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory

namespace SRWTightness

theorem cosineMoment_origin_recurrence (n : ℕ) :
    cosineMoment (n + 2) 0 = ((n : ℝ) + 1) / ((n : ℝ) + 2) * cosineMoment n 0 := by
  simp only [cosineMoment, Int.cast_zero, zero_mul, Real.cos_zero, mul_one,
    fourierInterval_integral_eq_intervalIntegral]
  rw [integral_cos_pow]
  simp

theorem cosineMoment_origin_even (n : ℕ) :
    cosineMoment (2 * n) 0 = 2 * Real.pi * (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp [cosineMoment_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, cosineMoment_origin_recurrence, ih]
    have hb : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
        2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    push_cast
    rw [pow_succ]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
    have hp : (4 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    nlinarith [hb]

theorem cosineMoment_origin_odd (n : ℕ) : cosineMoment (2 * n + 1) 0 = 0 := by
  induction n with
  | zero =>
    simp only [Nat.mul_zero, zero_add, cosineMoment, pow_one, Int.cast_zero, zero_mul,
      Real.cos_zero, mul_one, fourierInterval_integral_eq_intervalIntegral]
    simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      cosineMoment_origin_recurrence, ih, mul_zero]

end SRWTightness
