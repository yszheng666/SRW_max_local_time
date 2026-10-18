import SRWTightness.HarmonicGaussianRegression

namespace SRWTightness

/-- Diagonal flatness and increment bounds control the actual regression coefficient. -/
theorem finite_gaussian_regression_coefficient_bound {ι : Type*} (S : Matrix ι ι ℝ)
    (o x : ι) (C : ℝ) (hv : 0 < S o o)
    (hdiag : |S x x - S o o| ≤ C)
    (hinc0 : 0 ≤ S x x + S o o - 2 * S x o)
    (hinc : S x x + S o o - 2 * S x o ≤ C) :
    |S x o / S o o - 1| ≤ C / S o o := by
  have hd := abs_le.mp hdiag
  have hb : |S x o - S o o| ≤ C := by
    rw [abs_le]
    constructor <;> linarith
  have he : S x o / S o o - 1 = (S x o - S o o) / S o o := by
    field_simp
  rw [he, abs_div, abs_of_pos hv]
  exact div_le_div_of_nonneg_right hb hv.le

/-- A positive regression coefficient close to one is dominated by one Gaussian positive part. -/
theorem gaussian_regression_pointwise_domination (b v C t u : ℝ)
    (hv : 0 < v) (hCv : C ≤ v) (hb : |b - 1| ≤ C / v) :
    b * t + u ≤ (1 + C / v) * max t 0 + |u| := by
  have hbd := abs_le.mp hb
  have hratio : C / v ≤ 1 := (div_le_iff₀ hv).mpr (by simpa using hCv)
  have hb0 : 0 ≤ b := by linarith only [hbd.1, hratio]
  have hb1 : b ≤ 1 + C / v := by linarith only [hbd.2]
  by_cases ht : 0 ≤ t
  · rw [max_eq_left ht]
    exact add_le_add (mul_le_mul_of_nonneg_right hb1 ht) (le_abs_self u)
  · rw [max_eq_right (le_of_not_ge ht), mul_zero]
    have hm := mul_nonpos_of_nonneg_of_nonpos hb0 (le_of_not_ge ht)
    linarith [le_abs_self u]

/-- The enlarged Gaussian coordinate changes variance by a bounded amount. -/
theorem gaussian_regression_enlarged_variance (v C : ℝ)
    (hv : 0 < v) (hC : 0 ≤ C) (hCv : C ≤ v) :
    v ≤ (1 + C / v) ^ 2 * v ∧ (1 + C / v) ^ 2 * v ≤ v + 3 * C := by
  have he : (1 + C / v) ^ 2 * v = v + 2 * C + C ^ 2 / v := by
    field_simp
    <;> ring
  have hq : C ^ 2 / v ≤ C := by
    rw [div_le_iff₀ hv]
    nlinarith [mul_le_mul_of_nonneg_left hCv hC]
  have hq0 : 0 ≤ C ^ 2 / v := div_nonneg (sq_nonneg C) hv.le
  rw [he]
  constructor <;> linarith only [hq, hq0, hC]

end SRWTightness
