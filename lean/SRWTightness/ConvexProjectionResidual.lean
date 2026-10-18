import SRWTightness.ConvexNearestPoint
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Abel

open scoped InnerProductSpace

namespace SRWTightness

/-- The constructed nearest point realizes the metric distance to the convex set. -/
theorem convexNearestPoint_infDist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    Metric.infDist x K = ‖x - convexNearestPoint K hne hcomplete hconvex x‖ := by
  rw [Metric.infDist_eq_iInf, convexNearestPoint_minimizes]
  simp only [dist_eq_norm]

/-- The residual from projection is itself firmly nonexpansive. -/
theorem convexProjectionResidual_firm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x y : E) :
    ‖(x - convexNearestPoint K hne hcomplete hconvex x) -
      (y - convexNearestPoint K hne hcomplete hconvex y)‖ ^ 2 ≤
      ⟪x - y, (x - convexNearestPoint K hne hcomplete hconvex x) -
        (y - convexNearestPoint K hne hcomplete hconvex y)⟫_ℝ := by
  let p := convexNearestPoint K hne hcomplete hconvex x
  let q := convexNearestPoint K hne hcomplete hconvex y
  have hh := convexNearestPoint_firm K hne hcomplete hconvex x y
  have he : (x - p) - (y - q) = (x - y) - (p - q) := by abel
  change ‖(x - p) - (y - q)‖ ^ 2 ≤ ⟪x - y, (x - p) - (y - q)⟫_ℝ
  rw [he, norm_sub_sq_real, inner_sub_right (x - y) (x - y) (p - q),
    real_inner_self_eq_norm_sq]
  linarith

/-- The residual mapping has Lipschitz constant one, without a factor-two loss. -/
theorem convexProjectionResidual_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) :
    LipschitzWith 1 (fun x ↦ x - convexNearestPoint K hne hcomplete hconvex x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hh := (convexProjectionResidual_firm K hne hcomplete hconvex x y).trans
    (real_inner_le_norm _ _)
  nlinarith [norm_nonneg (x - y), norm_nonneg
    ((x - convexNearestPoint K hne hcomplete hconvex x) -
      (y - convexNearestPoint K hne hcomplete hconvex y))]

/-- A point satisfying the variational condition is the selected nearest point. -/
theorem convexNearestPoint_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x z : E) (hz : z ∈ K) (hv : ∀ w ∈ K, ⟪x - z, w - z⟫_ℝ ≤ 0) :
    convexNearestPoint K hne hcomplete hconvex x = z := by
  let p := convexNearestPoint K hne hcomplete hconvex x
  have h1 := convexNearestPoint_variational K hne hcomplete hconvex x z hz
  have h2 := hv p (convexNearestPoint_mem K hne hcomplete hconvex x)
  have he := real_inner_self_eq_norm_sq (p - z)
  have hnorm : ‖p - z‖ ^ 2 ≤ 0 := by
    change ⟪x - p, z - p⟫_ℝ ≤ 0 at h1
    simp only [inner_sub_left, inner_sub_right] at h1 h2 he
    simp only [real_inner_comm z p] at h1 h2 he
    linarith
  have hzero : ‖p - z‖ = 0 := by nlinarith [norm_nonneg (p - z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Projection fixes points of the convex set. -/
theorem convexNearestPoint_of_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x : E) (hx : x ∈ K) : convexNearestPoint K hne hcomplete hconvex x = x := by
  apply convexNearestPoint_unique K hne hcomplete hconvex x x hx
  intro w hw
  simp

end SRWTightness
