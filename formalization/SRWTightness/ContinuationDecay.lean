import SRWTightness.SourceCoarseExponentExpansion

namespace SRWTightness

/-- The logarithmic correction cancels the time-square normalization in the continuation bound. -/
theorem continuation_exponential_decay (t d ν x E K : ℝ) (ht : 0 < t)
    (hE : 2 * t - 2 * d - 2 * Real.log t + 2 * ν - 2 * x - K ≤ E) :
    Real.exp (-2 * d) * Real.exp (-E) / t ^ 2 ≤
      Real.exp K * Real.exp (-2 * t - 2 * ν + 2 * x) := by
  have hlog : t ^ 2 = Real.exp (Real.log t + Real.log t) := by
    rw [Real.exp_add, Real.exp_log ht]
    ring
  rw [hlog, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The initial-height prefactor has the source three-halves growth in the early generation. -/
theorem continuation_initial_prefactor (ν θ x : ℝ) (hν : 0 ≤ ν) (hθ : θ ≤ 4)
    (hx : x ≤ 4 + θ * ν) :
    (ν + 1) * Real.sqrt x ≤ 2 * (ν + 1) ^ (3 / 2 : ℝ) := by
  have hθν := mul_le_mul_of_nonneg_right hθ hν
  have hroot : Real.sqrt x ≤ 2 * Real.sqrt (ν + 1) := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.sqrt (ν + 1))).mpr
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ ν + 1)]
    nlinarith
  have hrpow : (ν + 1) ^ (3 / 2 : ℝ) = (ν + 1) * Real.sqrt (ν + 1) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith : 0 < ν + 1), Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hrpow]
  nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ ν + 1 by linarith)]

end SRWTightness
