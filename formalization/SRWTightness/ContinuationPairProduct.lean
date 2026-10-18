import SRWTightness.ContinuationDecay

namespace SRWTightness

/-- Multiplying the two literal continuation bounds gives the prefactor and joint exponential
weight in equation 8.11, without any probabilistic independence assumption. -/
theorem continuation_pair_product_bound (C ν t x y p q : ℝ)
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hq0 : 0 ≤ q)
    (hp : p ≤ C * (ν + 1) ^ (3 / 2 : ℝ) / (Real.exp t) ^ 2 *
      Real.exp (-2 * ν + 2 * x))
    (hq : q ≤ C * (ν + 1) ^ (3 / 2 : ℝ) / (Real.exp t) ^ 2 *
      Real.exp (-2 * ν + 2 * y)) :
    p * q ≤ C ^ 2 * (ν + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
      Real.exp (2 * x + 2 * y) := by
  have hm := mul_le_mul hp hq hq0 (by positivity :
    0 ≤ C * (ν + 1) ^ (3 / 2 : ℝ) / (Real.exp t) ^ 2 * Real.exp (-2 * ν + 2 * x))
  have hhalf : (ν + 1) ^ (3 / 2 : ℝ) = (ν + 1) * Real.sqrt (ν + 1) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith : 0 < ν + 1), Real.rpow_one, Real.sqrt_eq_rpow]
  have hsq : ((ν + 1) ^ (3 / 2 : ℝ)) ^ 2 = (ν + 1) ^ 3 := by
    rw [hhalf, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ ν + 1)]
    ring
  apply hm.trans_eq
  calc
    _ = C ^ 2 * ((ν + 1) ^ (3 / 2 : ℝ)) ^ 2 / (Real.exp t) ^ 4 *
        (Real.exp (-2 * ν + 2 * x) * Real.exp (-2 * ν + 2 * y)) := by ring
    _ = C ^ 2 * (ν + 1) ^ 3 / (Real.exp t) ^ 4 *
        (Real.exp (-4 * ν) * Real.exp (2 * x + 2 * y)) := by
      rw [hsq, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ = _ := by ring

end SRWTightness
