import SRWTightness.SourceRootReturnRate
import SRWTightness.SourceTerminalThresholdUniform

namespace SRWTightness

/-- The actual terminal radius absorbs the return numerator error uniformly over all k<=t. -/
theorem source_return_error_small (K A : ℝ) (hK : 0 ≤ K) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ k : ℕ, (k : ℝ) ≤ t →
      A ≤ sourceLowerRadius t - 14 ∧
      K * ((k : ℝ) + sourceRootReturnShift) ≤ sourceLowerRadius t - 14 := by
  refine ⟨max (sourceScaleThreshold 4) (max 4 (max K (max sourceRootReturnShift (A + 14)))), ?_⟩
  intro t ht k hk
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_left _ _).trans ht
  have h1 := (le_max_right _ _).trans ht
  have ht4 : 4 ≤ t := (le_max_left _ _).trans h1
  have h2 := (le_max_right _ _).trans h1
  have hKt : K ≤ t := (le_max_left _ _).trans h2
  have h3 := (le_max_right _ _).trans h2
  have hCt : sourceRootReturnShift ≤ t := (le_max_left _ _).trans h3
  have hAt : A + 14 ≤ t := (le_max_right _ _).trans h3
  have hm := sourceLowerRadius_ge_seventh_power t htbase
  have ht7 : t ≤ t ^ 7 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ t) (by norm_num : 1 ≤ 7)
  have ht3 : t ^ 3 ≤ t ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hpoly : 2 * t ^ 2 + 14 ≤ t ^ 3 := by
    nlinarith [sq_nonneg (t - 4), mul_nonneg (by linarith : 0 ≤ t - 4) (sq_nonneg t)]
  have hp := mul_le_mul_of_nonneg_left
    (show (k : ℝ) + sourceRootReturnShift ≤ 2 * t by linarith) hK
  have hp' := mul_le_mul_of_nonneg_right hKt (by linarith : 0 ≤ 2 * t)
  constructor <;> nlinarith

end SRWTightness
