import SRWTightness.GaussianField

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace

namespace SRWTightness

 theorem gaussianGreenLaw_linear_mean (D A : Finset Site) (u : EuclideanSpace ℝ A) :
    (∫ φ : EuclideanSpace ℝ A, ⟪u, φ⟫ ∂gaussianGreenLaw D A) = 0 := by
  have he := (innerSL ℝ u).integral_comp_id_comm
    (IsGaussian.integrable_id (μ := gaussianGreenLaw D A))
  change (∫ φ : EuclideanSpace ℝ A, ⟪u, φ⟫ ∂gaussianGreenLaw D A) =
    (innerSL ℝ u) (∫ φ, φ ∂gaussianGreenLaw D A) at he
  rw [gaussianGreenLaw_mean, map_zero] at he
  exact he

 theorem gaussianGreenLaw_linear_covariance (D A : Finset Site) (hAD : A ⊆ D)
    (u v : EuclideanSpace ℝ A) :
    covariance (fun φ : EuclideanSpace ℝ A ↦ ⟪u, φ⟫)
      (fun φ : EuclideanSpace ℝ A ↦ ⟪v, φ⟫) (gaussianGreenLaw D A) =
      u ⬝ᵥ (observationGreen D A).mulVec v := by
  rw [← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ := gaussianGreenLaw D A))]
  exact covarianceBilin_multivariateGaussian (observationGreen_posDef D A hAD).posSemidef u v

 theorem gaussianGreenLaw_linear_variance (D A : Finset Site) (hAD : A ⊆ D)
    (u : EuclideanSpace ℝ A) :
    variance (fun φ : EuclideanSpace ℝ A ↦ ⟪u, φ⟫) (gaussianGreenLaw D A) =
      u ⬝ᵥ (observationGreen D A).mulVec u := by
  rw [← covariance_self (by fun_prop), gaussianGreenLaw_linear_covariance D A hAD]

 theorem gaussianGreenLaw_linear_gaussian (D A : Finset Site) (hAD : A ⊆ D)
    (u : EuclideanSpace ℝ A) :
    (gaussianGreenLaw D A).map (fun φ : EuclideanSpace ℝ A ↦ ⟪u, φ⟫) =
      gaussianReal 0 (u ⬝ᵥ (observationGreen D A).mulVec u).toNNReal := by
  have he := IsGaussian.map_eq_gaussianReal (μ := gaussianGreenLaw D A) (innerSL ℝ u)
  change (gaussianGreenLaw D A).map (fun φ : EuclideanSpace ℝ A ↦ ⟪u, φ⟫) =
    gaussianReal (∫ φ : EuclideanSpace ℝ A, ⟪u, φ⟫ ∂gaussianGreenLaw D A)
      (variance (fun φ : EuclideanSpace ℝ A ↦ ⟪u, φ⟫) (gaussianGreenLaw D A)).toNNReal at he
  rw [gaussianGreenLaw_linear_mean, gaussianGreenLaw_linear_variance D A hAD] at he
  exact he

end SRWTightness
