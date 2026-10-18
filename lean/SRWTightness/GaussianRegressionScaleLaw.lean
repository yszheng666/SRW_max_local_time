import SRWTightness.HarmonicRegressionBounds

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Real scaling of the actual centered Gaussian law has the exact scaled variance. -/
theorem gaussian_real_scaled_variance (s v : ℝ) :
    (gaussianReal 0 v.toNNReal).map (fun t ↦ s * t) =
      gaussianReal 0 (s ^ 2 * v).toNNReal := by
  rw [gaussianReal_map_const_mul, mul_zero, Real.toNNReal_mul (sq_nonneg s),
    Real.toNNReal_of_nonneg (sq_nonneg s)]

/-- The enlarged harmonic coordinate is a measure-preserving Gaussian scaling. -/
theorem gaussian_regression_scale_preserving (v C : ℝ) :
    MeasurePreserving (fun t : ℝ ↦ (1 + C / v) * t) (gaussianReal 0 v.toNNReal)
      (gaussianReal 0 ((1 + C / v) ^ 2 * v).toNNReal) := by
  exact ⟨by fun_prop, gaussian_real_scaled_variance _ _⟩

end SRWTightness
