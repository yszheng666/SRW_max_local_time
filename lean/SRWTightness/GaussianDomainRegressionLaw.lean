import SRWTightness.HarmonicGaussianRegression

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Reconstruct the actual larger-domain field from independent fine, scalar and residual laws. -/
theorem gaussian_domain_regression_reconstruction (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o : E)
    (hv : 0 < (observationGreen D E - greenMatrix E) o o) :
    ((gaussianGreenLaw E E).prod
      ((gaussianReal 0 ((observationGreen D E - greenMatrix E) o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o)))).map
      (fun p ↦ p.1 + finiteGaussianRegressionRebuild
        (observationGreen D E - greenMatrix E) o p.2) = gaussianGreenLaw D E := by
  have hR : MeasurePreserving
      (finiteGaussianRegressionRebuild (observationGreen D E - greenMatrix E) o)
      ((gaussianReal 0 ((observationGreen D E - greenMatrix E) o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o)))
      (harmonicGaussianLaw D E) := by
    refine ⟨?_, (harmonic_gaussian_regression hReg D E hED o hv).2⟩
    unfold finiteGaussianRegressionRebuild
    fun_prop
  have hP := (MeasurePreserving.id (gaussianGreenLaw E E)).prod hR
  rw [← gaussian_domain_decomposition D E hED, ← hP.map_eq,
    Measure.map_map (by fun_prop) hP.measurable]
  rfl

/-- Normalizing the actual reconstructed field preserves the exact larger-domain Green law. -/
theorem gaussian_domain_regression_normalized (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o : E) (σ : ℝ)
    (hv : 0 < (observationGreen D E - greenMatrix E) o o) :
    ((gaussianGreenLaw E E).prod
      ((gaussianReal 0 ((observationGreen D E - greenMatrix E) o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o)))).map
      (fun p ↦ σ⁻¹ • p.1 + σ⁻¹ • finiteGaussianRegressionRebuild
        (observationGreen D E - greenMatrix E) o p.2) =
      (gaussianGreenLaw D E).map (fun φ ↦ σ⁻¹ • φ) := by
  rw [← gaussian_domain_regression_reconstruction hReg D E hED o hv,
    Measure.map_map (by fun_prop) (by unfold finiteGaussianRegressionRebuild; fun_prop)]
  congr 1
  funext p
  exact (smul_add σ⁻¹ p.1
    (finiteGaussianRegressionRebuild (observationGreen D E - greenMatrix E) o p.2)).symm

end SRWTightness
