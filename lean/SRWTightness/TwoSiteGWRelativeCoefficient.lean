import SRWTightness.TwoSiteGWWeightedCoefficient

namespace SRWTightness

/-- Fixed relative endpoint and row bounds suffice for positivity of the combined GW coefficient. -/
theorem twoSiteOptimizedTilt_gw_coefficient_of_ratios (g D B y α j d : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hB : 0 < B) (hy : 0 < y)
    (hj : 0 ≤ j) (hd : 0 < d) (hα : g ≤ α)
    (hDu : D ≤ (11 / 10 : ℝ) * d) (hBu : B ≤ (5 / 2 : ℝ) * j)
    (hgap : (3 / 2 : ℝ) * d ≤ y - B) :
    0 < α * twoSiteOptimizedTilt g D B y /
      (1 - g * D * twoSiteOptimizedTilt g D B y) - 1 / (2 * (j + 1)) := by
  apply twoSiteOptimizedTilt_gw_coefficient_pos g D B y α (j + 1) hg hD hB hy (by linarith)
  have hprod := mul_le_mul hDu hBu hB.le (by positivity : 0 ≤ (11 / 10 : ℝ) * d)
  have hlo : g * ((3 / 2 : ℝ) * d) ≤ α * (y - B) :=
    mul_le_mul hα hgap (by positivity) (by linarith)
  calc
    g * D * B ≤ g * ((11 / 4 : ℝ) * d * j) := by
      have hh := mul_le_mul_of_nonneg_left hprod hg.le
      nlinarith only [hh]
    _ < g * (3 * (j + 1) * d) := by
      apply mul_lt_mul_of_pos_left _ hg
      nlinarith [mul_nonneg hj hd.le]
    _ ≤ 2 * (j + 1) * α * (y - B) := by
      have hh := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ 2 * (j + 1))
      nlinarith only [hh]

end SRWTightness
