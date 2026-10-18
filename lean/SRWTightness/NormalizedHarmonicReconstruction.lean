import SRWTightness.NormalizedGreenRegression

open MeasureTheory ProbabilityTheory
namespace SRWTightness

noncomputable def normalizedHarmonicCov (D E : Finset Site) (σ : ℝ) : Matrix E E ℝ :=
  σ⁻¹ ^ 2 • (observationGreen D E - greenMatrix E)

theorem normalizedHarmonicCov_posSemidef (D E : Finset Site) (hED : E ⊆ D) (σ : ℝ) :
    (normalizedHarmonicCov D E σ).PosSemidef :=
  (green_difference_posSemidef D E hED).smul (sq_nonneg σ⁻¹)

/-- Normalize only the harmonic factor, while retaining the original fine-field law. -/
theorem normalized_fine_harmonic_decomposition (D E : Finset Site) (hED : E ⊆ D) (σ : ℝ) :
    ((gaussianGreenLaw E E).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ E) (normalizedHarmonicCov D E σ))).map
        (fun p ↦ σ⁻¹ • p.1 + p.2) =
      (gaussianGreenLaw D E).map (fun φ ↦ σ⁻¹ • φ) := by
  have hN : MeasurePreserving (fun φ : EuclideanSpace ℝ E ↦ σ⁻¹ • φ)
      (harmonicGaussianLaw D E)
      (multivariateGaussian 0 (normalizedHarmonicCov D E σ)) :=
    ⟨by fun_prop, normalized_harmonic_green_law D E hED σ⟩
  have hP := (MeasurePreserving.id (gaussianGreenLaw E E)).prod hN
  rw [← hP.map_eq, Measure.map_map (by fun_prop) hP.measurable,
    ← gaussian_domain_decomposition D E hED, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  exact (smul_add σ⁻¹ p.1 p.2).symm

/-- Regress the normalized harmonic matrix, matching the scalar variance used by the tail bound. -/
theorem normalized_harmonic_regression_reconstruction (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o : E) (σ : ℝ)
    (hv : 0 < normalizedHarmonicCov D E σ o o) :
    ((gaussianGreenLaw E E).prod
      ((gaussianReal 0 (normalizedHarmonicCov D E σ o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o)))).map
      (fun p ↦ σ⁻¹ • p.1 +
        finiteGaussianRegressionRebuild (normalizedHarmonicCov D E σ) o p.2) =
      (gaussianGreenLaw D E).map (fun φ ↦ σ⁻¹ • φ) := by
  have hR : MeasurePreserving
      (finiteGaussianRegressionRebuild (normalizedHarmonicCov D E σ) o)
      ((gaussianReal 0 (normalizedHarmonicCov D E σ o o).toNNReal).prod
        (multivariateGaussian (0 : EuclideanSpace ℝ E)
          (finiteGaussianRegressionCov (normalizedHarmonicCov D E σ) o)))
      (multivariateGaussian 0 (normalizedHarmonicCov D E σ)) := by
    refine ⟨?_, (hReg E _ o (normalizedHarmonicCov_posSemidef D E hED σ) hv).2⟩
    unfold finiteGaussianRegressionRebuild
    fun_prop
  have hP := (MeasurePreserving.id (gaussianGreenLaw E E)).prod hR
  rw [← normalized_fine_harmonic_decomposition D E hED σ, ← hP.map_eq,
    Measure.map_map (by fun_prop) hP.measurable]
  rfl

end SRWTightness
