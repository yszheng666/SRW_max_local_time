import SRWTightness.TwoSiteOptimizedTilt

namespace SRWTightness

/-- The standard logarithmic lower bound follows directly from mathlib's rational bound. -/
theorem log_one_add_quadratic_lower (W : ℝ) (hW : 0 ≤ W) :
    W - W ^ 2 / 2 ≤ Real.log (1 + W) := by
  calc
    W - W ^ 2 / 2 ≤ 2 * W / (W + 2) := by
      apply (le_div_iff₀ (by linarith : 0 < W + 2)).mpr
      nlinarith [pow_nonneg hW 3]
    _ ≤ Real.log (1 + W) := Real.le_log_one_add_of_nonneg hW

/-- Every permitted endpoint uses the same tilt and is bounded by the largest endpoint deficit. -/
theorem twoSiteOptimizedTilt_exponent (g D B y α b u : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hB : 0 < B) (hBy : B < y)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hub : u ≤ b)
    (hmatch : α * b ^ 2 = g * B ^ 2) :
    -g * y ^ 2 * Real.log (1 + twoSiteOptimizedTilt g D B y) +
      α * u ^ 2 * twoSiteOptimizedTilt g D B y /
        (1 - g * D * twoSiteOptimizedTilt g D B y) ≤
      -(y - B) ^ 2 / D + g * y ^ 2 * (twoSiteOptimizedTilt g D B y) ^ 2 / 2 := by
  let W := twoSiteOptimizedTilt g D B y
  have ha := twoSiteOptimizedTilt_admissible g D B y hg hD hB hBy
  have hW : 0 ≤ W := ha.1.le
  have hden : 0 ≤ 1 - g * D * W := by dsimp [W]; linarith [ha.2]
  have husq : u ^ 2 ≤ b ^ 2 := by nlinarith
  have hmono := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left husq hα) hW) hden
  have hlog := mul_le_mul_of_nonneg_left (log_one_add_quadratic_lower W hW)
    (mul_nonneg hg.le (sq_nonneg y))
  have he := twoSiteOptimizedTilt_quadratic g D B y α b hg hD hB (by linarith) hmatch
  change -g * y ^ 2 * Real.log (1 + W) + α * u ^ 2 * W / (1 - g * D * W) ≤
    -(y - B) ^ 2 / D + g * y ^ 2 * W ^ 2 / 2
  change -g * y ^ 2 * W + α * b ^ 2 * W / (1 - g * D * W) = -(y - B) ^ 2 / D at he
  nlinarith only [hmono, hlog, he]

end SRWTightness
