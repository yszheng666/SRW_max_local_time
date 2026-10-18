import SRWTightness.SRWFourierProduct
import SRWTightness.CosineMomentCoefficient

namespace SRWTightness

/-- Exact binomial formula at every accessible endpoint, in rotated coordinates. -/
theorem transitionProbability_binomial (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n) (z : Site)
    (hz1 : z.1 + z.2 = 2 * (j : ℤ) - n) (hz2 : z.1 - z.2 = 2 * (l : ℤ) - n) :
    transitionProbability n z = (n.choose j : ℝ) * (n.choose l : ℝ) / 4 ^ n := by
  rw [transitionProbability_product, hz1, hz2, cosineMoment_coefficient n j hj,
    cosineMoment_coefficient n l hl]
  have hpow : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [hpow]
  have hp := Real.pi_ne_zero
  field_simp
  <;> ring

theorem transitionProbability_binomial_site (n j l : ℕ) (hj : j ≤ n) (hl : l ≤ n) :
    transitionProbability n ((j : ℤ) + l - n, (j : ℤ) - l) =
      (n.choose j : ℝ) * (n.choose l : ℝ) / 4 ^ n := by
  apply transitionProbability_binomial n j l hj hl
  · dsimp; ring
  · dsimp; ring

end SRWTightness
