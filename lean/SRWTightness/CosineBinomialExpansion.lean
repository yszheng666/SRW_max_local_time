import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Finset

namespace SRWTightness

theorem complex_exp_imaginary_re (t : ℝ) : (Complex.exp ((t : ℂ) * Complex.I)).re = Real.cos t := by
  rw [← Complex.cos_add_sin_I]
  simp [Complex.cos_ofReal_re]

theorem cosine_power_binomial_expansion (n : ℕ) (t : ℝ) :
    (2 * Real.cos t) ^ n = ∑ j ∈ range (n + 1),
      Real.cos (((2 * j : ℕ) : ℝ) * t - (n : ℝ) * t) * (n.choose j : ℝ) := by
  have hs : Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I) =
      ((2 * Real.cos t : ℝ) : ℂ) := by
    rw [← Complex.cos_add_sin_I, ← Complex.cos_sub_sin_I]
    push_cast
    ring
  have hb := add_pow (Complex.exp ((t : ℂ) * Complex.I))
    (Complex.exp (-(t : ℂ) * Complex.I)) n
  rw [hs] at hb
  have he (j : ℕ) (hj : j ∈ range (n + 1)) :
      Complex.exp ((t : ℂ) * Complex.I) ^ j * Complex.exp (-(t : ℂ) * Complex.I) ^ (n - j) =
      Complex.exp (((((2 * j : ℕ) : ℝ) * t - (n : ℝ) * t) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    push_cast [Nat.cast_sub hjn]
    ring
  have hr := congrArg Complex.re hb
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_sum] at hr
  rw [hr]
  apply sum_congr rfl
  intro j hj
  rw [he j hj]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero,
    complex_exp_imaginary_re]

end SRWTightness
