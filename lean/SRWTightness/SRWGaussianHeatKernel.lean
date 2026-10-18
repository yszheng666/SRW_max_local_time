import SRWTightness.BinomialGaussianCoordinates
import SRWTightness.SRWReachableCoordinates
import SRWTightness.SRWBinomialTransition
import SRWTightness.SRWReturnBounds

namespace SRWTightness

/-- A global Gaussian upper bound for the original planar SRW at even times. -/
theorem transitionProbability_even_gaussian_le (n : ℕ) (hn : 0 < n) (z : Site) :
    transitionProbability (2 * n) z ≤
      (1 / (Real.pi * n)) * Real.exp (-(normSq z / (4 * n))) := by
  by_cases hz : ∃ j ≤ 2 * n, ∃ l ≤ 2 * n, z = ((j : ℤ) + l - (2 * n : ℕ), (j : ℤ) - l)
  · obtain ⟨j, hj, l, hl, rfl⟩ := hz
    rw [transitionProbability_binomial_site (2 * n) j l hj hl]
    have hc : (Nat.centralBinom n : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
    have hp : (4 : ℝ) ^ n ≠ 0 := by positivity
    have hfact : ((2 * n).choose j : ℝ) * ((2 * n).choose l : ℝ) / 4 ^ (2 * n) =
        centralBinomialRatio n ^ 2 *
          ((((2 * n).choose j : ℝ) / (Nat.centralBinom n : ℝ)) *
            (((2 * n).choose l : ℝ) / (Nat.centralBinom n : ℝ))) := by
      unfold centralBinomialRatio
      rw [show 2 * n = n * 2 by omega, pow_mul]
      field_simp
      <;> ring
    rw [hfact]
    calc
      _ ≤ centralBinomialRatio n ^ 2 *
          (Real.exp (-(((j : ℝ) - n) ^ 2 / (2 * n))) *
            Real.exp (-(((l : ℝ) - n) ^ 2 / (2 * n)))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul (binomial_coefficient_le_gaussian n j hj hn)
          (binomial_coefficient_le_gaussian n l hl hn) (by positivity) (Real.exp_nonneg _)
      _ = centralBinomialRatio n ^ 2 *
          Real.exp (-(normSq ((j : ℤ) + l - (2 * n : ℕ), (j : ℤ) - l) / (4 * n))) := by
        rw [← Real.exp_add]
        congr 2
        unfold normSq
        push_cast
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        simpa only [transitionProbability_return_even] using transitionProbability_return_le n hn
  · rw [transitionProbability_eq_zero_of_unreachable (2 * n) z hz]
    positivity

end SRWTightness
