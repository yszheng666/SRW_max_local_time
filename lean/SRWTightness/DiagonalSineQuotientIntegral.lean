import SRWTightness.DiagonalTrigonometricSum

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- The diagonal cosine quotient integrates to four times the finite odd harmonic sum. -/
theorem diagonal_sine_quotient_integral (n : ℕ) :
    (∫ u in 0..Real.pi, (1 - Real.cos (2 * (n : ℝ) * u)) / Real.sin u) =
      4 * ∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1) := by
  have he : (∫ u in 0..Real.pi, (1 - Real.cos (2 * (n : ℝ) * u)) / Real.sin u) =
      ∫ u in 0..Real.pi, 2 * ∑ j ∈ Finset.range n,
        Real.sin ((2 * (j : ℝ) + 1) * u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(volume : Measure ℝ).ae_ne Real.pi] with u hupi hu
    have hu' : u ∈ Set.Ioc (0 : ℝ) Real.pi := by
      simpa only [Set.uIoc_of_le Real.pi_pos.le] using hu
    have hs : Real.sin u ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi hu'.1 (lt_of_le_of_ne hu'.2 hupi))
    rw [diagonal_trigonometric_sum, mul_div_cancel_right₀ _ hs]
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum]
  · simp_rw [odd_sine_integral]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

end SRWTightness
