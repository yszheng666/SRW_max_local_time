import SRWTightness.ConvexDistanceDerivative
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

namespace SRWTightness

/-- Away from a complete convex set, distance has the unit-residual derivative. -/
theorem convexDistance_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x : E) (hx : 0 < Metric.infDist x K) :
    HasFDerivAt (fun y ↦ Metric.infDist y K)
      ((Metric.infDist x K)⁻¹ • innerSL ℝ (x - convexNearestPoint K hne hcomplete hconvex x)) x := by
  have hh := (convexDistanceSquared_hasFDerivAt K hne hcomplete hconvex x).sqrt
    (pow_ne_zero 2 hx.ne')
  have he : (fun y : E ↦ Real.sqrt (Metric.infDist y K ^ 2)) =
      (fun y : E ↦ Metric.infDist y K) := by
    funext y
    exact Real.sqrt_sq Metric.infDist_nonneg
  rw [he, Real.sqrt_sq Metric.infDist_nonneg, smul_smul] at hh
  have hc : (1 / (2 * Metric.infDist x K)) * 2 = (Metric.infDist x K)⁻¹ := by
    field_simp
  rwa [hc] at hh

theorem convexDistance_fderiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x : E) (hx : 0 < Metric.infDist x K) :
    fderiv ℝ (fun y ↦ Metric.infDist y K) x =
      (Metric.infDist x K)⁻¹ • innerSL ℝ (x - convexNearestPoint K hne hcomplete hconvex x) :=
  (convexDistance_hasFDerivAt K hne hcomplete hconvex x hx).fderiv

/-- The derivative of distance has norm exactly one outside the set. -/
theorem convexDistance_fderiv_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x : E) (hx : 0 < Metric.infDist x K) :
    ‖fderiv ℝ (fun y ↦ Metric.infDist y K) x‖ = 1 := by
  rw [convexDistance_fderiv K hne hcomplete hconvex x hx, norm_smul, innerSL_apply_norm,
    ← convexNearestPoint_infDist K hne hcomplete hconvex x,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx), inv_mul_cancel₀ hx.ne']

end SRWTightness
