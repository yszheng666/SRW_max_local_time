import SRWTightness.DiagonalSineQuotientIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- The one-dimensional angular quotient arising from the diagonal potential. -/
noncomputable def diagonalAbsoluteQuotient (n : ℕ) (u : ℝ) : ℝ :=
  (1 - Real.cos (2 * (n : ℝ) * u)) / |Real.sin u|

/-- The absolute-sine quotient has period pi at every integer diagonal frequency. -/
theorem diagonalAbsoluteQuotient_periodic (n : ℕ) :
    Function.Periodic (diagonalAbsoluteQuotient n) Real.pi := by
  intro u
  have hc : Real.cos (2 * (n : ℝ) * (u + Real.pi)) = Real.cos (2 * (n : ℝ) * u) := by
    rw [show 2 * (n : ℝ) * (u + Real.pi) =
      2 * (n : ℝ) * u + n * (2 * Real.pi) by ring]
    exact Real.cos_add_nat_mul_two_pi _ n
  simp only [diagonalAbsoluteQuotient, hc, Real.sin_add_pi, abs_neg]

/-- The quotient is integrable on its basic half-circle despite its endpoint denominator zeros. -/
theorem diagonalAbsoluteQuotient_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (diagonalAbsoluteQuotient n) volume 0 Real.pi := by
  have hc : Continuous (fun u : ℝ ↦ 2 * ∑ j ∈ Finset.range n,
      Real.sin ((2 * (j : ℝ) + 1) * u)) := by fun_prop
  apply (hc.intervalIntegrable 0 Real.pi).congr_uIoo
  intro u hu
  have hu' : u ∈ Set.Ioo (0 : ℝ) Real.pi := by
    simpa only [Set.uIoo_of_le Real.pi_pos.le] using hu
  have hs := Real.sin_pos_of_pos_of_lt_pi hu'.1 hu'.2
  unfold diagonalAbsoluteQuotient
  rw [abs_of_pos hs, diagonal_trigonometric_sum, mul_div_cancel_right₀ _ (ne_of_gt hs)]

/-- One half-circle gives four times the odd harmonic sum. -/
theorem diagonalAbsoluteQuotient_half_integral (n : ℕ) :
    (∫ u in 0..Real.pi, diagonalAbsoluteQuotient n u) =
      4 * ∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1) := by
  rw [← diagonal_sine_quotient_integral n]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Set.Icc (0 : ℝ) Real.pi := by
    simpa only [Set.uIcc_of_le Real.pi_pos.le] using hu
  simp only [diagonalAbsoluteQuotient,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu'.1 hu'.2)]

/-- The complete-period diagonal quotient has its exact finite harmonic-sum integral. -/
theorem diagonalAbsoluteQuotient_integral (n : ℕ) :
    (∫ u in 0..2 * Real.pi, diagonalAbsoluteQuotient n u) =
      8 * ∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1) := by
  have hp := diagonalAbsoluteQuotient_periodic n
  have hi := hp.intervalIntegrable₀ Real.pi_ne_zero
    (diagonalAbsoluteQuotient_intervalIntegrable n)
  have he := hp.intervalIntegral_add_zsmul_eq 2 0 hi
  simp only [zsmul_eq_mul, Int.cast_ofNat, zero_add] at he
  rw [he, diagonalAbsoluteQuotient_half_integral]
  ring

end SRWTightness
