import SRWTightness.CosineBinomialExpansion
import SRWTightness.CosineProductOrthogonality

open MeasureTheory Finset

namespace SRWTightness

theorem cosineMoment_binomial_sum (n : ℕ) (k : ℤ) :
    (2 : ℝ) ^ n * cosineMoment n k = Real.pi * ∑ j ∈ range (n + 1),
      (n.choose j : ℝ) * ((if 2 * (j : ℤ) - n + k = 0 then 1 else 0) +
        (if 2 * (j : ℤ) - n - k = 0 then 1 else 0)) := by
  have he (t : ℝ) : (2 : ℝ) ^ n * (Real.cos t ^ n * Real.cos ((k : ℝ) * t)) =
      ∑ j ∈ range (n + 1),
        (Real.cos (((2 * (j : ℤ) - n : ℤ) : ℝ) * t) * Real.cos ((k : ℝ) * t)) * (n.choose j : ℝ) := by
    rw [← mul_assoc, ← mul_pow, cosine_power_binomial_expansion, sum_mul]
    apply sum_congr rfl
    intro j hj
    push_cast
    rw [show 2 * (j : ℝ) * t - (n : ℝ) * t = (2 * (j : ℝ) - n) * t by ring]
    ring
  unfold cosineMoment
  rw [← integral_const_mul]
  simp_rw [he]
  rw [integral_finsetSum (range (n + 1))]
  · simp_rw [integral_mul_const, fourierInterval_integral_cos_mul]
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  · intro j hj
    exact (show Continuous (fun t : ℝ ↦
      (Real.cos (((2 * (j : ℤ) - n : ℤ) : ℝ) * t) * Real.cos ((k : ℝ) * t)) * (n.choose j : ℝ))
      by fun_prop).integrableOn_Icc

end SRWTightness
