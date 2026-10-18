import SRWTightness.ConvexDistanceTaylor
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.NormNum

open Filter Asymptotics
open scoped Topology InnerProductSpace

namespace SRWTightness

/-- Squared distance has derivative twice the inner product with the projection residual. -/
theorem convexDistanceSquared_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) :
    HasFDerivAt (fun y ↦ Metric.infDist y K ^ 2)
      ((2 : ℝ) • innerSL ℝ (x - convexNearestPoint K hne hcomplete hconvex x)) x := by
  rw [hasFDerivAt_iff_isLittleO]
  apply IsBigO.trans_isLittleO (g := fun y : E ↦ ‖y - x‖ ^ 2) _
    (isLittleO_pow_sub_sub x (by norm_num : 1 < (2 : ℕ)))
  apply IsBigO.of_bound'
  filter_upwards with y
  have hh := convexDistanceSquared_remainder K hne hcomplete hconvex x y
  change ‖Metric.infDist y K ^ 2 - Metric.infDist x K ^ 2 -
    2 * ⟪x - convexNearestPoint K hne hcomplete hconvex x, y - x⟫_ℝ‖ ≤ ‖‖y - x‖ ^ 2‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh.1, abs_of_nonneg (sq_nonneg _)]
  exact hh.2

theorem convexDistanceSquared_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) :
    fderiv ℝ (fun y ↦ Metric.infDist y K ^ 2) x =
      (2 : ℝ) • innerSL ℝ (x - convexNearestPoint K hne hcomplete hconvex x) :=
  (convexDistanceSquared_hasFDerivAt K hne hcomplete hconvex x).fderiv

/-- The derivative of squared distance is globally 2-Lipschitz. -/
theorem convexDistanceSquared_fderiv_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) :
    LipschitzWith 2 (fderiv ℝ (fun y ↦ Metric.infDist y K ^ 2)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [convexDistanceSquared_fderiv K hne hcomplete hconvex, dist_eq_norm,
    ← smul_sub, ← map_sub, norm_smul, innerSL_apply_norm, NNReal.coe_ofNat]
  have hh := (convexProjectionResidual_lipschitz K hne hcomplete hconvex).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hh
  simpa only [Real.norm_ofNat] using mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2 by norm_num)

end SRWTightness
