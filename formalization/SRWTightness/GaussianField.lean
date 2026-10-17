import SRWTightness.GreenPositive
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Centered Gaussian field on a finite observation set with the actual killed SRW Green covariance. -/
noncomputable def gaussianGreenLaw (D A : Finset Site) : Measure (EuclideanSpace ℝ A) :=
  multivariateGaussian 0 (observationGreen D A)

instance gaussianGreenLaw_isGaussian (D A : Finset Site) : IsGaussian (gaussianGreenLaw D A) := by
  unfold gaussianGreenLaw
  infer_instance

instance gaussianGreenLaw_isProbabilityMeasure (D A : Finset Site) :
    IsProbabilityMeasure (gaussianGreenLaw D A) := by infer_instance

 theorem gaussianGreenLaw_mean (D A : Finset Site) :
    (∫ φ, φ ∂gaussianGreenLaw D A) = 0 := integral_id_multivariateGaussian

 theorem gaussianGreenLaw_covariance (D A : Finset Site) (hAD : A ⊆ D) (y z : A) :
    covariance (fun φ : EuclideanSpace ℝ A ↦ φ y) (fun φ : EuclideanSpace ℝ A ↦ φ z)
      (gaussianGreenLaw D A) = killedGreen D y z :=
  covariance_eval_multivariateGaussian (observationGreen_posDef D A hAD).posSemidef y z

 theorem gaussianGreenLaw_coordinate (D A : Finset Site) (hAD : A ⊆ D) (z : A) :
    MeasurePreserving (fun φ : EuclideanSpace ℝ A ↦ φ z) (gaussianGreenLaw D A)
      (gaussianReal 0 (killedGreen D z z).toNNReal) := by
  exact measurePreserving_eval_multivariateGaussian (observationGreen_posDef D A hAD).posSemidef

 theorem gaussianGreenLaw_restrict (D A K : Finset Site) (hAK : A ⊆ K) (hKD : K ⊆ D) :
    MeasurePreserving (EuclideanSpace.restrict₂ hAK) (gaussianGreenLaw D K)
      (gaussianGreenLaw D A) := by
  have he := measurePreserving_restrict₂_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ K)) (observationGreen_posDef D K hKD).posSemidef hAK
  have hs : (observationGreen D K).submatrix (fun i : A ↦ ⟨i.1, hAK i.2⟩)
      (fun i : A ↦ ⟨i.1, hAK i.2⟩) = observationGreen D A := rfl
  rw [hs, map_zero] at he
  exact he

end SRWTightness
