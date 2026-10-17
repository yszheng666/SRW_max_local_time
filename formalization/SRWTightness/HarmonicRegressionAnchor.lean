import SRWTightness.HarmonicGaussianRegression

open MeasureTheory ProbabilityTheory Matrix
namespace SRWTightness

/-- The regression residual is almost surely zero at the reference point. -/
theorem finite_gaussian_regression_anchor_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (o : ι) (hv : 0 < S o o)
    (hS : (finiteGaussianRegressionCov S o).PosSemidef) :
    ∀ᵐ φ ∂multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o),
      φ o = 0 := by
  have hm := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ ι)) (i := o) hS
  apply ae_of_ae_map
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o))
    (p := fun y : ℝ ↦ y = 0) hm.measurable.aemeasurable
  rw [hm.map_eq]
  simp [finite_gaussian_regression_anchor S o hv, gaussianReal_zero_var]

/-- The actual harmonic residual satisfies the anchor condition needed for increment estimates. -/
theorem harmonic_gaussian_regression_anchor_ae (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o : E)
    (hv : 0 < (observationGreen D E - greenMatrix E) o o) :
    ∀ᵐ φ ∂multivariateGaussian (0 : EuclideanSpace ℝ E)
      (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o), φ o = 0 := by
  exact finite_gaussian_regression_anchor_ae _ o hv
    (harmonic_gaussian_regression hReg D E hED o hv).1

end SRWTightness
