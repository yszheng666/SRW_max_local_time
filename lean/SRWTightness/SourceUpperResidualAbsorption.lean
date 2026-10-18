import SRWTightness.SourceUpperGaussianPrefactor

namespace SRWTightness

/-- The polynomial in the residual tail is absorbed by half its quadratic Gaussian cost. -/
theorem source_upper_residual_polynomial (c h a : ℝ) (hc : 0 < c) (hh : 1 ≤ h) :
    (1 + a) * Real.exp (-(c * a ^ 2 / (2 * h))) ≤ (2 + 2 / c) * h := by
  have hh0 : 0 < h := by linarith
  let u := c * a ^ 2 / (2 * h)
  let K := 2 + 2 / c
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hK2 : 2 ≤ K := by dsimp [K]; linarith [div_pos (by norm_num : (0 : ℝ) < 2) hc]
  have hconst : 2 ≤ K * h := hK2.trans (by nlinarith only [hh, hK])
  have hcoef : 2 * h / c ≤ K * h := by
    dsimp [K]
    have he : (2 + 2 / c) * h = 2 * h + 2 * h / c := by ring
    rw [he]
    linarith
  have heq : (2 * h / c) * u = a ^ 2 := by
    dsimp [u]
    field_simp
  have hquad := mul_le_mul_of_nonneg_right hcoef hu
  rw [heq] at hquad
  have hpoly : 1 + a ≤ K * h * (1 + u) := by
    nlinarith [sq_nonneg (a - 1 / 2)]
  have hexp : 1 + a ≤ K * h * Real.exp u := hpoly.trans
    (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp u]) (by positivity))
  have hm := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-u))
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hm
  exact hm

/-- The spare variance exponential dominates the inverse-square-root prefactor. -/
theorem source_upper_residual_variance (v : ℝ) (hv : 0 < v) :
    Real.exp (-2 * v) ≤ 1 / Real.sqrt v := by
  have hs : Real.sqrt v ≤ 1 + 2 * v := by
    have he := Real.sq_sqrt hv.le
    have hn := Real.sqrt_nonneg v
    nlinarith [sq_nonneg (Real.sqrt v - 1)]
  have he : Real.sqrt v ≤ Real.exp (2 * v) := hs.trans (by linarith [Real.add_one_le_exp (2 * v)])
  have hb := one_div_le_one_div_of_le (Real.sqrt_pos.2 hv) he
  simpa only [one_div, Real.exp_neg, neg_mul] using hb

end SRWTightness
