import SRWTightness.RelativeProbabilityUpper

namespace SRWTightness

/-- A fixed positive lower comparison extends the sharp relative-error exponent to every size. -/
theorem relative_probability_wide_exponential (p q ε c : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) (hc : 0 < c)
    (hr : |p - q| ≤ ε * q) (hl : c * q ≤ p) :
    Real.exp (-(2 * (1 + |Real.log c|) * ε)) * q ≤ p ∧
      p ≤ Real.exp (2 * (1 + |Real.log c|) * ε) * q := by
  let A : ℝ := 2 * (1 + |Real.log c|)
  have hA : 2 ≤ A := by dsimp [A]; nlinarith [abs_nonneg (Real.log c)]
  have hAε : 2 * ε ≤ A * ε := mul_le_mul_of_nonneg_right hA hε
  constructor
  · by_cases hs : ε ≤ 1 / 2
    · have hb := (relative_probability_exponential p q ε hq hε hs hr).1
      exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hAε)) hq).trans hb
    · have he : -A * ε ≤ Real.log c := by
        have hhalf : 1 / 2 ≤ ε := (lt_of_not_ge hs).le
        have hp := mul_le_mul_of_nonneg_right hhalf (abs_nonneg (Real.log c))
        have hn := neg_le_abs (Real.log c)
        dsimp [A]
        nlinarith [abs_nonneg (Real.log c)]
      have hexp : Real.exp (-(A * ε)) ≤ c := by
        rw [← Real.exp_log hc]
        apply Real.exp_le_exp.mpr
        simpa only [neg_mul] using he
      exact (mul_le_mul_of_nonneg_right hexp hq).trans hl
  · have hb := relative_probability_exponential_upper p q ε hq hr
    have he : ε ≤ A * ε := by linarith
    exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) hq)

end SRWTightness
