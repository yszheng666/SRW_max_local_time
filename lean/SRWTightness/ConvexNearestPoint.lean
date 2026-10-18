import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

open scoped InnerProductSpace

namespace SRWTightness

noncomputable def convexNearestPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x : E) : E := (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose

theorem convexNearestPoint_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    convexNearestPoint K hne hcomplete hconvex x ∈ K :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose_spec.1

theorem convexNearestPoint_minimizes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    ‖x - convexNearestPoint K hne hcomplete hconvex x‖ = ⨅ w : K, ‖x - w‖ :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x).choose_spec.2

theorem convexNearestPoint_variational {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x z : E) (hz : z ∈ K) :
    ⟪x - convexNearestPoint K hne hcomplete hconvex x,
      z - convexNearestPoint K hne hcomplete hconvex x⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconvex
    (convexNearestPoint_mem K hne hcomplete hconvex x)).mp
      (convexNearestPoint_minimizes K hne hcomplete hconvex x) z hz

/-- The projection satisfies the stronger, inner-product form of nonexpansiveness. -/
theorem convexNearestPoint_firm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x y : E) :
    ‖convexNearestPoint K hne hcomplete hconvex x - convexNearestPoint K hne hcomplete hconvex y‖ ^ 2 ≤
      ⟪x - y, convexNearestPoint K hne hcomplete hconvex x -
        convexNearestPoint K hne hcomplete hconvex y⟫_ℝ := by
  let p := convexNearestPoint K hne hcomplete hconvex x
  let q := convexNearestPoint K hne hcomplete hconvex y
  have hx := convexNearestPoint_variational K hne hcomplete hconvex x q
    (convexNearestPoint_mem K hne hcomplete hconvex y)
  have hy := convexNearestPoint_variational K hne hcomplete hconvex y p
    (convexNearestPoint_mem K hne hcomplete hconvex x)
  have he := real_inner_self_eq_norm_sq (p - q)
  change ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ
  change ⟪x - p, q - p⟫_ℝ ≤ 0 at hx
  change ⟪y - q, p - q⟫_ℝ ≤ 0 at hy
  simp only [inner_sub_left, inner_sub_right] at hx hy he ⊢
  simp only [real_inner_comm q p] at hx hy he ⊢
  linarith

/-- Projection onto a nonempty complete convex set is 1-Lipschitz. -/
theorem convexNearestPoint_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K) :
    LipschitzWith 1 (convexNearestPoint K hne hcomplete hconvex) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have hh := (convexNearestPoint_firm K hne hcomplete hconvex x y).trans
    (real_inner_le_norm _ _)
  nlinarith [norm_nonneg (x - y), norm_nonneg
    (convexNearestPoint K hne hcomplete hconvex x - convexNearestPoint K hne hcomplete hconvex y)]

end SRWTightness
