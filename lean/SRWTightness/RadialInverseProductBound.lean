import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- Two nonzero unshifted coordinates dominate the inverse radial norm by a product. -/
theorem radial_inverse_product_bound (c a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Real.sqrt (c ^ 2 + a ^ 2 + b ^ 2))⁻¹ ≤
      |a| ^ (-(1 / 2 : ℝ)) * |b| ^ (-(1 / 2 : ℝ)) := by
  have hA := Real.sqrt_pos.mpr (abs_pos.mpr ha)
  have hB := Real.sqrt_pos.mpr (abs_pos.mpr hb)
  have hC : 0 < Real.sqrt |a| * Real.sqrt |b| := mul_pos hA hB
  have hsq : (Real.sqrt |a| * Real.sqrt |b|) ^ 2 = |a| * |b| := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg a), Real.sq_sqrt (abs_nonneg b)]
  have hsum : 0 ≤ c ^ 2 + a ^ 2 + b ^ 2 := by positivity
  have hlarge : Real.sqrt |a| * Real.sqrt |b| ≤ Real.sqrt (c ^ 2 + a ^ 2 + b ^ 2) := by
    have hab := sq_nonneg (|a| - |b|)
    have haa := sq_abs a
    have hbb := sq_abs b
    nlinarith [Real.sq_sqrt hsum, Real.sqrt_nonneg (c ^ 2 + a ^ 2 + b ^ 2), sq_nonneg c]
  have hh := one_div_le_one_div_of_le hC hlarge
  rw [Real.rpow_neg (abs_nonneg a), Real.rpow_neg (abs_nonneg b),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simpa only [one_div, mul_inv_rev, mul_comm] using hh

end SRWTightness
