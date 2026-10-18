import SRWTightness.GaussianDomainRegressionLaw
import SRWTightness.GaussianScalarCovariance

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The normalized three-factor reconstruction has exactly the normalized SRW Green covariance. -/
theorem normalized_green_regression_law (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o : E) (σ : ℝ)
    (hv : 0 < (observationGreen D E - greenMatrix E) o o) :
    ((gaussianGreenLaw E E).prod
      ((gaussianReal 0 ((observationGreen D E - greenMatrix E) o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o)))).map
      (fun p ↦ σ⁻¹ • p.1 + σ⁻¹ • finiteGaussianRegressionRebuild
        (observationGreen D E - greenMatrix E) o p.2) =
      multivariateGaussian (0 : EuclideanSpace ℝ E) (σ⁻¹ ^ 2 • observationGreen D E) := by
  rw [gaussian_domain_regression_normalized hReg D E hED o σ hv]
  exact multivariateGaussian_zero_smul (observationGreen D E)
    (observationGreen_posDef D E hED).posSemidef σ⁻¹

/-- The normalized harmonic field retains the actual scaled Green difference. -/
theorem normalized_harmonic_green_law (D E : Finset Site) (hED : E ⊆ D) (σ : ℝ) :
    (harmonicGaussianLaw D E).map (fun φ ↦ σ⁻¹ • φ) =
      multivariateGaussian (0 : EuclideanSpace ℝ E)
        (σ⁻¹ ^ 2 • (observationGreen D E - greenMatrix E)) :=
  multivariateGaussian_zero_smul _ (green_difference_posSemidef D E hED) σ⁻¹

end SRWTightness
