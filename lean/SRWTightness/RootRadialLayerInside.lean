import SRWTightness.RootOuterDomainGeometry

namespace SRWTightness

/-- A root's full unit-thickness exit layer lies in the killing disk under the geometric margin. -/
theorem root_radial_layer_inside (b : Site) (c R : ℝ) (hc : 0 ≤ c)
    (hfit : Real.sqrt (normSq b) + c + 1 < R) (y : Site)
    (hy : Real.sqrt (normSq (y - b)) ≤ c + 1) : y ∈ diskFinset R := by
  have hb := Real.sqrt_nonneg (normSq b)
  have hn := Real.sqrt_nonneg (normSq (y - b))
  have hs := Real.sq_sqrt (normSq_nonneg (y - b))
  have hbound := normSq_add_bound b (y - b) hb (by linarith : 0 ≤ c + 1)
    (le_of_eq (normSq_eq_sq_sqrt b)) (by nlinarith)
  rw [show b + (y - b) = y by abel] at hbound
  apply (mem_diskFinset R y).mpr
  exact hbound.trans_lt ((sq_lt_sq₀ (by positivity) (by linarith)).mpr (by linarith))

end SRWTightness
