import SRWTightness.ExternalBridgeReflection
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A centered bridge's intermediate value has its exact Gaussian variance. -/
theorem interval_bridge_intermediate_law (T r : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T) :
    HasLaw (actualIntervalBridge T r) (gaussianReal 0 (r * (T - r) / T).toNNReal)
      gaussianCoefficientLaw := by
  have hg := (actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval ⟨r, hr, hrT⟩
  have hv : Var[actualIntervalBridge T r; gaussianCoefficientLaw] = r * (T - r) / T := by
    rw [← covariance_self (actualIntervalBridge_measurable T r).aemeasurable,
      actualIntervalBridge_covariance T r r hT hr hrT hr hrT, min_self]
    field_simp
    <;> ring
  refine ⟨(actualIntervalBridge_measurable T r).aemeasurable, ?_⟩
  have he := hg.map_eq_gaussianReal
  rw [actualIntervalBridge_mean T r hT hr hrT, hv] at he
  exact he

/-- A bridge with a prescribed endpoint has the exact Gaussian intermediate distribution. -/
theorem endpoint_bridge_intermediate_law (T b r : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T) :
    HasLaw (endpointBrownianBridge T b r)
      (gaussianReal (r / T * b) (r * (T - r) / T).toNNReal) gaussianCoefficientLaw := by
  unfold endpointBrownianBridge
  simpa only [zero_add] using
    gaussianReal_add_const (interval_bridge_intermediate_law T r hT hr hrT) (r / T * b)

end SRWTightness
