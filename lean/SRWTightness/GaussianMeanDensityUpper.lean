import SRWTightness.GaussianTranslation

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- A pointwise Gaussian density comparison survives a common mean and independent variables. -/
theorem gaussian_mean_density_event_upper {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (S K : Matrix ι ι ℝ) (hS : S.PosDef) (hK : K.PosDef)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, gaussianCovarianceDensity S x ≤
      ENNReal.ofReal C * gaussianCovarianceDensity K x)
    (mean : ι → ℝ) (E : Set ((ι → ℝ) × Ξ)) (hE : MeasurableSet E) :
    ((gaussianMeanCoordinateLaw mean S).prod ν).real E ≤
      C * ((gaussianMeanCoordinateLaw mean K).prod ν).real E := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hμ : gaussianCoordinateLaw S ≤ ENNReal.ofReal C • gaussianCoordinateLaw K := by
    unfold gaussianCoordinateLaw
    rw [multivariateGaussian_coordinate_density _ hS,
      multivariateGaussian_coordinate_density _ hK,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    exact withDensity_mono (Filter.Eventually.of_forall hbound)
  have hprod := Measure.prod_mono hμ (le_refl ν)
  rw [Measure.prod_smul_left] at hprod
  rw [gaussianMeanCoordinateLaw_prod_real ν mean S E hE,
    gaussianMeanCoordinateLaw_prod_real ν mean K E hE]
  have hh := hprod ((fun p ↦ (mean + p.1, p.2)) ⁻¹' E)
  have hreal := ENNReal.toReal_mono (by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hh
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC, Measure.real] using hreal

end SRWTightness
