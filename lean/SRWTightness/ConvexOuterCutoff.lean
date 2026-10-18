import SRWTightness.ConvexDistanceGradientVariation
import SRWTightness.ScaledQuadraticCutoff
import Mathlib.Analysis.Calculus.FDeriv.Mul

open Filter
open scoped Topology

namespace SRWTightness

noncomputable def convexOuterCutoff {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (ε : ℝ) (x : E) : ℝ := scaledQuadraticCutoff ε (Metric.infDist x K)

theorem convexOuterCutoff_bounds {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (ε : ℝ) (x : E) :
    0 ≤ convexOuterCutoff K ε x ∧ convexOuterCutoff K ε x ≤ 1 :=
  scaledQuadraticCutoff_bounds ε (Metric.infDist x K)

theorem convexOuterCutoff_eq_one {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : Metric.infDist x K = 0) :
    convexOuterCutoff K ε x = 1 :=
  scaledQuadraticCutoff_eq_one ε _ hε hx.le

theorem convexOuterCutoff_eq_zero {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : ε ≤ Metric.infDist x K) :
    convexOuterCutoff K ε x = 0 := scaledQuadraticCutoff_eq_zero ε _ hε hx

/-- Close to the set the cutoff is exactly a quadratic polynomial of metric distance. -/
theorem convexOuterCutoff_near_formula {E : Type*} [PseudoMetricSpace E]
    (K : Set E) (ε : ℝ) (hε : 0 < ε) (x : E) (hx : Metric.infDist x K ≤ ε / 2) :
    convexOuterCutoff K ε x = 1 - (2 / ε ^ 2) * Metric.infDist x K ^ 2 := by
  have h0 : 0 ≤ Metric.infDist x K / ε := div_nonneg Metric.infDist_nonneg hε.le
  have h1 : Metric.infDist x K / ε ≤ 1 / 2 := (div_le_iff₀ hε).mpr (by linarith)
  have he : quadraticCutoff (Metric.infDist x K / ε) =
      1 - 2 * (Metric.infDist x K / ε) ^ 2 := by
    unfold quadraticCutoff
    split_ifs <;> nlinarith
  unfold convexOuterCutoff scaledQuadraticCutoff
  rw [he]
  ring

/-- At zero distance, squared-distance differentiability makes the outer cutoff derivative zero. -/
theorem convexOuterCutoff_hasFDerivAt_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (x : E)
    (hx : Metric.infDist x K = 0) :
    HasFDerivAt (convexOuterCutoff K ε) (0 : E →L[ℝ] ℝ) x := by
  have hr : x - convexNearestPoint K hne hcomplete hconvex x = 0 := by
    apply norm_eq_zero.mp
    rw [← convexNearestPoint_infDist K hne hcomplete hconvex x, hx]
  have hsq := convexDistanceSquared_hasFDerivAt K hne hcomplete hconvex x
  have hp := (hsq.const_mul (2 / ε ^ 2)).const_sub 1
  have hp0 : HasFDerivAt (fun y ↦ 1 - (2 / ε ^ 2) * Metric.infDist y K ^ 2)
      (0 : E →L[ℝ] ℝ) x := by simpa [hr] using hp
  apply hp0.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, Metric.infDist y K < ε / 2 :=
    (Metric.continuous_infDist_pt K).continuousAt.tendsto.eventually
      (eventually_lt_nhds (show Metric.infDist x K < ε / 2 by rw [hx]; positivity))
  filter_upwards [hn] with y hy
  exact convexOuterCutoff_near_formula K ε hε y hy.le

/-- The actual outer cutoff is differentiable everywhere, including the convex-set boundary. -/
theorem convexOuterCutoff_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (x : E) :
    HasFDerivAt (convexOuterCutoff K ε)
      ((quadraticCutoffSlope (Metric.infDist x K / ε) / ε) •
        fderiv ℝ (fun y ↦ Metric.infDist y K) x) x := by
  by_cases hx : Metric.infDist x K = 0
  · simpa [hx, quadraticCutoffSlope] using
      convexOuterCutoff_hasFDerivAt_zero K hne hcomplete hconvex ε hε x hx
  · have hx0 : 0 < Metric.infDist x K := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hx)
    have hd := convexDistance_hasFDerivAt K hne hcomplete hconvex x hx0
    rw [hd.fderiv]
    exact (scaledQuadraticCutoff_hasDerivAt ε (Metric.infDist x K)).comp_hasFDerivAt x hd

/-- The derivative of the actual outer cutoff has norm at most two over the smoothing scale. -/
theorem convexOuterCutoff_fderiv_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (ε : ℝ) (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (convexOuterCutoff K ε) x‖ ≤ 2 / ε := by
  rw [(convexOuterCutoff_hasFDerivAt K hne hcomplete hconvex ε hε x).fderiv]
  by_cases hx : Metric.infDist x K = 0
  · simp only [hx, zero_div, quadraticCutoffSlope, le_refl, if_true, zero_smul, norm_zero]
    positivity
  · have hx0 : 0 < Metric.infDist x K := lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hx)
    rw [norm_smul, convexDistance_fderiv_norm K hne hcomplete hconvex x hx0, mul_one,
      Real.norm_eq_abs]
    simpa only [scaledQuadraticCutoff_deriv] using
      scaledQuadraticCutoff_deriv_bound ε (Metric.infDist x K) hε

end SRWTightness
