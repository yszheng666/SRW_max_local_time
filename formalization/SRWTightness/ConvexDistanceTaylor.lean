import SRWTightness.ConvexProjectionResidual

open scoped InnerProductSpace

namespace SRWTightness

/-- Squared distance to a convex set has a nonnegative, quadratically bounded Taylor remainder. -/
theorem convexDistanceSquared_remainder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x y : E) :
    0 ≤ Metric.infDist y K ^ 2 - Metric.infDist x K ^ 2 -
      2 * ⟪x - convexNearestPoint K hne hcomplete hconvex x, y - x⟫_ℝ ∧
    Metric.infDist y K ^ 2 - Metric.infDist x K ^ 2 -
      2 * ⟪x - convexNearestPoint K hne hcomplete hconvex x, y - x⟫_ℝ ≤ ‖y - x‖ ^ 2 := by
  let p := convexNearestPoint K hne hcomplete hconvex x
  let q := convexNearestPoint K hne hcomplete hconvex y
  rw [convexNearestPoint_infDist K hne hcomplete hconvex y,
    convexNearestPoint_infDist K hne hcomplete hconvex x]
  change 0 ≤ ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ ∧
    ‖y - q‖ ^ 2 - ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - x⟫_ℝ ≤ ‖y - x‖ ^ 2
  constructor
  · have hv := convexNearestPoint_variational K hne hcomplete hconvex x q
      (convexNearestPoint_mem K hne hcomplete hconvex y)
    change ⟪x - p, q - p⟫_ℝ ≤ 0 at hv
    have he : y - x = ((y - q) - (x - p)) + (q - p) := by abel
    rw [he, inner_add_right, inner_sub_right, real_inner_self_eq_norm_sq]
    have hn := norm_sub_sq_real (y - q) (x - p)
    rw [← real_inner_comm (y - q) (x - p)] at hn
    nlinarith [sq_nonneg ‖(y - q) - (x - p)‖]
  · have hm := Metric.infDist_le_dist_of_mem (x := y)
      (convexNearestPoint_mem K hne hcomplete hconvex x)
    rw [convexNearestPoint_infDist K hne hcomplete hconvex y, dist_eq_norm] at hm
    have hs := (sq_le_sq₀ (norm_nonneg (y - q)) (norm_nonneg (y - p))).mpr hm
    have he : y - p = (x - p) + (y - x) := by abel
    rw [he, norm_add_sq_real] at hs
    linarith

end SRWTightness
