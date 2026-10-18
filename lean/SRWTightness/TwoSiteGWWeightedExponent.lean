import SRWTightness.TwoSiteOptimizedExponent

namespace SRWTightness

/-- A nonnegative combined quadratic coefficient puts the largest GW-weighted term at the endpoint. -/
theorem twoSiteOptimizedTilt_gw_weighted_exponent (g D B y α q u s : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hB : 0 < B) (hBy : B < y)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (huq : u ≤ q)
    (hmatch : α * q ^ 2 = g * B ^ 2)
    (hcoeff : 0 ≤ α * twoSiteOptimizedTilt g D B y /
      (1 - g * D * twoSiteOptimizedTilt g D B y) - 1 / (2 * s)) :
    -u ^ 2 / (2 * s) + (-g * y ^ 2 * Real.log (1 + twoSiteOptimizedTilt g D B y) +
      α * u ^ 2 * twoSiteOptimizedTilt g D B y /
        (1 - g * D * twoSiteOptimizedTilt g D B y)) ≤
      -q ^ 2 / (2 * s) - (y - B) ^ 2 / D +
        g * y ^ 2 * (twoSiteOptimizedTilt g D B y) ^ 2 / 2 := by
  have hsq : u ^ 2 ≤ q ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq hcoeff
  have hmono : -u ^ 2 / (2 * s) + α * u ^ 2 * twoSiteOptimizedTilt g D B y /
      (1 - g * D * twoSiteOptimizedTilt g D B y) ≤
      -q ^ 2 / (2 * s) + α * q ^ 2 * twoSiteOptimizedTilt g D B y /
      (1 - g * D * twoSiteOptimizedTilt g D B y) := by
    calc
      _ = (α * twoSiteOptimizedTilt g D B y /
        (1 - g * D * twoSiteOptimizedTilt g D B y) - 1 / (2 * s)) * u ^ 2 := by ring
      _ ≤ (α * twoSiteOptimizedTilt g D B y /
        (1 - g * D * twoSiteOptimizedTilt g D B y) - 1 / (2 * s)) * q ^ 2 := hm
      _ = _ := by ring
  have he := twoSiteOptimizedTilt_exponent g D B y α q q hg hD hB hBy hα
    (by linarith) le_rfl hmatch
  simp only [neg_div] at hmono he ⊢
  linarith only [hmono, he]

end SRWTightness
