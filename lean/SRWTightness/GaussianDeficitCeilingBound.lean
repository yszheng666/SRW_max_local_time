import SRWTightness.PositiveGaussianUnitShift

namespace SRWTightness

/-- Rounding a deficit upward by at most one retains the original Gaussian square and decay. -/
theorem gaussian_deficit_rounding_exponent (x q z κ d L : ℝ)
    (hqz : q ≤ z) (hzq : z ≤ q + 1) (hu : 1 ≤ x - q)
    (hκ : 0 ≤ κ) (hd : 1 ≤ d) (hL : 0 < L) :
    Real.exp (-(x - q) ^ 2 / (2 * L) - 2 * q - (κ / 2) * (max q 0) ^ 2 / d) ≤
      Real.exp (2 + κ / 2) *
        Real.exp (-(x - z) ^ 2 / (2 * L) - 2 * z - (κ / 4) * (max z 0) ^ 2 / d) := by
  have hd0 : 0 < d := by linarith
  have huz : 0 ≤ x - z := by linarith
  have husq : (x - z) ^ 2 ≤ (x - q) ^ 2 := by nlinarith
  have hgauss := div_le_div_of_nonneg_right (neg_le_neg husq)
    (show 0 ≤ 2 * L by positivity)
  have hmax : max (z - 1) 0 ≤ max q 0 := max_le_max (by linarith) le_rfl
  have hsq : (max (z - 1) 0) ^ 2 ≤ (max q 0) ^ 2 := by
    nlinarith [le_max_right (z - 1) 0, le_max_right q 0]
  have hshift := (positive_square_unit_shift z).trans hsq
  have hdecay := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hshift (show 0 ≤ κ / 2 by positivity)) hd0.le
  have hr : (κ / 2) * ((max z 0) ^ 2 / 2 - 1) / d =
      (κ / 4) * (max z 0) ^ 2 / d - (κ / 2) / d := by ring
  rw [hr] at hdecay
  have hscale : (κ / 2) / d ≤ κ / 2 := div_le_self (by positivity) hd
  have he : -(x - q) ^ 2 / (2 * L) - 2 * q - (κ / 2) * (max q 0) ^ 2 / d ≤
      (2 + κ / 2) + (-(x - z) ^ 2 / (2 * L) - 2 * z -
        (κ / 4) * (max z 0) ^ 2 / d) := by linarith
  exact (Real.exp_le_exp.mpr he).trans_eq (Real.exp_add _ _)

/-- The entire supported Gaussian-deficit summand is controlled on the rounded-up lattice. -/
theorem gaussian_deficit_rounding_summand (S x q z κ d L : ℝ)
    (hqz : q ≤ z) (hzq : z ≤ q + 1) (hu : 1 ≤ x - q)
    (hκ : 0 ≤ κ) (hd : 1 ≤ d) (hL : 0 < L) (hS : 0 ≤ S + q) :
    (S + q) / d * (1 + max q 0 / Real.sqrt d) *
        Real.exp (-(x - q) ^ 2 / (2 * L) - 2 * q - (κ / 2) * (max q 0) ^ 2 / d) ≤
      Real.exp (2 + κ / 2) * ((S + z) / d * (1 + max z 0 / Real.sqrt d) *
        Real.exp (-(x - z) ^ 2 / (2 * L) - 2 * z - (κ / 4) * (max z 0) ^ 2 / d)) := by
  have hd0 : 0 < d := by linarith
  have hP : 0 ≤ (S + q) / d * (1 + max q 0 / Real.sqrt d) := by positivity
  have hlin : (S + q) / d ≤ (S + z) / d :=
    div_le_div_of_nonneg_right (by linarith) hd0.le
  have hmax : 1 + max q 0 / Real.sqrt d ≤ 1 + max z 0 / Real.sqrt d :=
    by
      simpa only [add_comm] using
        add_le_add_left (div_le_div_of_nonneg_right (max_le_max hqz le_rfl)
          (Real.sqrt_nonneg d)) 1
  have hSz : 0 ≤ S + z := by linarith
  have hprod := mul_le_mul hlin hmax (by positivity) (by positivity : 0 ≤ (S + z) / d)
  have he := gaussian_deficit_rounding_exponent x q z κ d L hqz hzq hu hκ hd hL
  calc
    _ ≤ ((S + q) / d * (1 + max q 0 / Real.sqrt d)) *
        (Real.exp (2 + κ / 2) * Real.exp (-(x - z) ^ 2 / (2 * L) - 2 * z -
          (κ / 4) * (max z 0) ^ 2 / d)) := mul_le_mul_of_nonneg_left he hP
    _ ≤ ((S + z) / d * (1 + max z 0 / Real.sqrt d)) *
        (Real.exp (2 + κ / 2) * Real.exp (-(x - z) ^ 2 / (2 * L) - 2 * z -
          (κ / 4) * (max z 0) ^ 2 / d)) := mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = _ := by ring

end SRWTightness
