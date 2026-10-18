import SRWTightness.GlobalBrownianConstruction
import SRWTightness.ScaledGaussianPathLaw
import SRWTightness.GaussianProcessLawUniqueness

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Every finite restriction of the actual global path has the original scaled Brownian path law. -/
theorem global_brownian_finite_horizon_law (T : ℝ) (hT : 0 < T) :
    gaussianCoefficientLaw.map
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ globalBrownianPath u ω) =
    gaussianCoefficientLaw.map
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)) := by
  apply gaussian_process_law_eq_of_mean_covariance gaussianCoefficientLaw _ _
    (globalBrownianPath_gaussian.comp_right (fun u : Set.Icc (0 : ℝ) T ↦ (u : ℝ)))
    (scaled_gaussian_path_process T hT)
  · exact measurable_pi_lambda _ (fun u ↦ globalBrownianPath_measurable u)
  · exact measurable_pi_lambda _ (fun _ ↦
      measurable_const.mul (gaussianDyadicPath_measurable _))
  · intro u
    change (∫ ω, globalBrownianPath u ω ∂gaussianCoefficientLaw) = _
    rw [globalBrownianPath_mean, integral_const_mul,
      (gaussianPath_eval_hasLaw (u / T) (div_nonneg u.property.1 hT.le)
        ((div_le_one hT).mpr u.property.2)).integral_eq,
      integral_id_gaussianReal, mul_zero]
  · intro u v
    change cov[globalBrownianPath u, globalBrownianPath v; gaussianCoefficientLaw] = _
    rw [globalBrownianPath_covariance u v u.property.1 v.property.1,
      scaled_gaussian_path_covariance T u v hT u.property.1 u.property.2
        v.property.1 v.property.2]

end SRWTightness
