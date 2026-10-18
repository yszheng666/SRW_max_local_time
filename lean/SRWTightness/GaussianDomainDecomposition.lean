import SRWTightness.GreenCovarianceMonotone
import SRWTightness.GaussianConvolution
import SRWTightness.GaussianField

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

noncomputable def harmonicGaussianLaw (D E : Finset Site) : Measure (EuclideanSpace ℝ E) :=
  multivariateGaussian 0 (observationGreen D E - greenMatrix E)

instance harmonicGaussianLaw_isGaussian (D E : Finset Site) :
    IsGaussian (harmonicGaussianLaw D E) := by unfold harmonicGaussianLaw; infer_instance

instance harmonicGaussianLaw_isProbabilityMeasure (D E : Finset Site) :
    IsProbabilityMeasure (harmonicGaussianLaw D E) := by infer_instance

theorem harmonicGaussianLaw_mean (D E : Finset Site) :
    (∫ φ, φ ∂harmonicGaussianLaw D E) = 0 := integral_id_multivariateGaussian

theorem harmonicGaussianLaw_covariance (D E : Finset Site) (hED : E ⊆ D) (x y : E) :
    covariance (fun φ : EuclideanSpace ℝ E ↦ φ x) (fun φ : EuclideanSpace ℝ E ↦ φ y)
      (harmonicGaussianLaw D E) = killedGreen D x y - killedGreen E x y :=
  covariance_eval_multivariateGaussian (green_difference_posSemidef D E hED) x y

/-- The larger-domain field restricted to E is the sum of independent centered Gaussian fields,
one having the exact zero-boundary Green covariance on E. -/
theorem gaussian_domain_decomposition (D E : Finset Site) (hED : E ⊆ D) :
    ((gaussianGreenLaw E E).prod (harmonicGaussianLaw D E)).map (fun p ↦ p.1 + p.2) =
      gaussianGreenLaw D E := by
  have he := multivariateGaussian_zero_add (greenMatrix E)
    (observationGreen D E - greenMatrix E) (greenMatrix_posDef E).posSemidef
      (green_difference_posSemidef D E hED)
  have hs : greenMatrix E + (observationGreen D E - greenMatrix E) = observationGreen D E := by abel
  rw [hs] at he
  exact he

end SRWTightness
