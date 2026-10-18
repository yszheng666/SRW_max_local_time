import SRWTightness.TwoSiteOptimizedTilt

namespace SRWTightness

/-- A linear deficit bound controls both the optimized tilt and its logarithmic quadratic cost. -/
theorem twoSiteOptimizedTilt_error_bound (g D B y L : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hB : 0 < B) (hBy : B < y)
    (hL : 0 ≤ L) (hgap : y - B ≤ L * D) :
    twoSiteOptimizedTilt g D B y ≤ L / (g * y) ∧
      g * y ^ 2 * (twoSiteOptimizedTilt g D B y) ^ 2 / 2 ≤ L ^ 2 / (2 * g) := by
  have hy : 0 < y := by linarith
  have hW := (twoSiteOptimizedTilt_admissible g D B y hg hD hB hBy).1
  have he : g * y * twoSiteOptimizedTilt g D B y = (y - B) / D := by
    unfold twoSiteOptimizedTilt
    field_simp
    <;> ring
  have hh : g * y * twoSiteOptimizedTilt g D B y ≤ L := by
    rw [he]
    exact (div_le_iff₀ hD).mpr hgap
  have hp : 0 ≤ g * y * twoSiteOptimizedTilt g D B y := by positivity
  constructor
  · apply (le_div_iff₀ (mul_pos hg hy)).mpr
    nlinarith only [hh]
  · have hs : (g * y * twoSiteOptimizedTilt g D B y) ^ 2 ≤ L ^ 2 := by
      nlinarith
    apply (le_div_iff₀ (by positivity : 0 < 2 * g)).mpr
    nlinarith only [hs]

end SRWTightness
