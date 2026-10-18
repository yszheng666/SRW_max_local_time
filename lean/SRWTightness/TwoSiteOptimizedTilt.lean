import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SRWTightness

/-- The common two-site tilt chosen at the largest permitted endpoint. -/
noncomputable def twoSiteOptimizedTilt (g D B y : ℝ) : ℝ := (1 - B / y) / (g * D)

/-- The optimized tilt lies strictly inside the resolvent convergence interval. -/
theorem twoSiteOptimizedTilt_admissible (g D B y : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hB : 0 < B) (hBy : B < y) :
    0 < twoSiteOptimizedTilt g D B y ∧ g * D * twoSiteOptimizedTilt g D B y < 1 := by
  have hy : 0 < y := by linarith
  have hb : B / y < 1 := (div_lt_one hy).mpr hBy
  have he : g * D * twoSiteOptimizedTilt g D B y = 1 - B / y := by
    unfold twoSiteOptimizedTilt
    field_simp
  constructor
  · exact div_pos (sub_pos.mpr hb) (mul_pos hg hD)
  · rw [he]
    have hh := div_pos hB hy
    linarith

/-- The quadratic approximation of the optimized exponent is the squared endpoint deficit. -/
theorem twoSiteOptimizedTilt_quadratic (g D B y α b : ℝ)
    (hg : 0 < g) (hD : 0 < D) (hB : 0 < B) (hy : 0 < y)
    (hmatch : α * b ^ 2 = g * B ^ 2) :
    -g * y ^ 2 * twoSiteOptimizedTilt g D B y +
      α * b ^ 2 * twoSiteOptimizedTilt g D B y /
        (1 - g * D * twoSiteOptimizedTilt g D B y) = -(y - B) ^ 2 / D := by
  rw [hmatch]
  have he : g * D * twoSiteOptimizedTilt g D B y = 1 - B / y := by
    unfold twoSiteOptimizedTilt
    field_simp
  rw [he, show 1 - (1 - B / y) = B / y by ring]
  unfold twoSiteOptimizedTilt
  field_simp
  <;> ring

end SRWTightness
