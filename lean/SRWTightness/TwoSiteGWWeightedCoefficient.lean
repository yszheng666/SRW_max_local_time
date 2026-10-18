import SRWTightness.TwoSiteOptimizedTilt

namespace SRWTightness

/-- The optimized combined coefficient is positive under an explicit endpoint-gap comparison. -/
theorem twoSiteOptimizedTilt_gw_coefficient_pos (g D B y α s : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hB : 0 < B) (hy : 0 < y) (hs : 0 < s)
    (hgap : g * D * B < 2 * s * α * (y - B)) :
    0 < α * twoSiteOptimizedTilt g D B y /
      (1 - g * D * twoSiteOptimizedTilt g D B y) - 1 / (2 * s) := by
  have he : g * D * twoSiteOptimizedTilt g D B y = 1 - B / y := by
    unfold twoSiteOptimizedTilt
    field_simp
  have hid : α * twoSiteOptimizedTilt g D B y /
      (1 - g * D * twoSiteOptimizedTilt g D B y) = α * (y - B) / (g * D * B) := by
    rw [he, show 1 - (1 - B / y) = B / y by ring]
    unfold twoSiteOptimizedTilt
    field_simp
    <;> ring
  rw [hid]
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ (by positivity : 0 < 2 * s) (by positivity : 0 < g * D * B)).mpr
  nlinarith only [hgap]

end SRWTightness
