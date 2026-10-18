import SRWTightness.ConvexDistanceOutside
import SRWTightness.NormalizedVectorDistance

namespace SRWTightness

/-- Distance gradients vary with the reciprocal of the smaller positive distance to the set. -/
theorem convexDistance_fderiv_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x y : E)
    (hx : 0 < Metric.infDist x K) (hy : 0 < Metric.infDist y K) :
    ‖fderiv ℝ (fun z ↦ Metric.infDist z K) x - fderiv ℝ (fun z ↦ Metric.infDist z K) y‖ ≤
      ‖x - y‖ / min (Metric.infDist x K) (Metric.infDist y K) := by
  let r := fun z ↦ z - convexNearestPoint K hne hcomplete hconvex z
  have hd (z : E) : Metric.infDist z K = ‖r z‖ :=
    convexNearestPoint_infDist K hne hcomplete hconvex z
  have hrx : r x ≠ 0 := norm_pos_iff.mp (by simpa only [hd] using hx)
  have hry : r y ≠ 0 := norm_pos_iff.mp (by simpa only [hd] using hy)
  have hlinear (a : ℝ) (z : E) : innerSL ℝ (a • z) = a • innerSL ℝ z := by
    ext w
    simp
  rw [convexDistance_fderiv K hne hcomplete hconvex x hx,
    convexDistance_fderiv K hne hcomplete hconvex y hy, ← hlinear, ← hlinear,
    ← map_sub, innerSL_apply_norm]
  change ‖(Metric.infDist x K)⁻¹ • r x - (Metric.infDist y K)⁻¹ • r y‖ ≤ _
  simp only [hd]
  have hh := normalized_vector_distance_le (r x) (r y) hrx hry
  have hl := (convexProjectionResidual_lipschitz K hne hcomplete hconvex).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hl
  exact hh.trans (div_le_div_of_nonneg_right hl (le_min (norm_nonneg _) (norm_nonneg _)))

/-- On any region a positive distance from the set, the gradient has a uniform Lipschitz bound. -/
theorem convexDistance_fderiv_lipschitzOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (a : ℝ) (ha : 0 < a) (x y : E)
    (hx : a ≤ Metric.infDist x K) (hy : a ≤ Metric.infDist y K) :
    ‖fderiv ℝ (fun z ↦ Metric.infDist z K) x - fderiv ℝ (fun z ↦ Metric.infDist z K) y‖ ≤
      ‖x - y‖ / a := by
  exact (convexDistance_fderiv_sub_le K hne hcomplete hconvex x y
    (ha.trans_le hx) (ha.trans_le hy)).trans
      (div_le_div_of_nonneg_left (norm_nonneg _) ha (le_min hx hy))

end SRWTightness
