import SRWTightness.ScaledGaussianContinuousReflection
import SRWTightness.ScaledGaussianFlatDisintegration
import SRWTightness.GaussianReflectionCdfIntegral

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Actual bridge barrier probabilities have the exact integrated reflection formula below q. -/
theorem bridge_reflection_integrated (T q b : ℝ) (hT : 0 < T)
    (hq : 0 < q) (hb : b < q) :
    (∫ a in Set.Iic b, gaussianCoefficientLaw.real (bridgeFlatEvent T a q)
      ∂gaussianReal 0 T.toNNReal) =
    ∫ a in Set.Iic b, (1 - Real.exp (-(2 * q * (q - a) / T)))
      ∂gaussianReal 0 T.toNNReal := by
  rw [← scaled_gaussian_flat_disintegration T q b hT,
    scaled_gaussian_flat_endpoint_cdf T q b hT hq hb,
    gaussian_real_set_integral_density _ _ measurableSet_Iic T hT,
    gaussian_reflection_cdf_integral T q b hT]

end SRWTightness
