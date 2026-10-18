import SRWTightness.FiniteGaussianPositiveMaximumLaw
import SRWTightness.GaussianRegressionScaleLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Reorder the independent fine field, reference Gaussian and residual field. -/
theorem product_reference_first {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (τ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite τ] :
    MeasurePreserving (fun p : α × (β × γ) ↦ (p.2.1, (p.1, p.2.2)))
      (μ.prod (ν.prod τ)) (ν.prod (μ.prod τ)) := by
  have h₁ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ν τ)
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod
    (MeasurePreserving.id τ)
  exact (measurePreserving_prodAssoc ν μ τ).comp (h₂.comp h₁)

/-- The actual law of the sum of the positive fine maximum and absolute residual maximum. -/
noncomputable def finiteGaussianMaximumResidualLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m : ℝ) : Measure ℝ :=
  ((finiteGaussianPositiveMaximumLaw S J hJ σ m).prod
    (finiteGaussianAbsMaximumLaw T J hJ)).map (fun p ↦ p.1 + p.2)

theorem finiteGaussianMaximumResidualLaw_isProbabilityMeasure {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S T : Matrix ι ι ℝ)
    (J : Finset ι) (hJ : J.Nonempty) (σ m : ℝ) :
    IsProbabilityMeasure (finiteGaussianMaximumResidualLaw S T J hJ σ m) := by
  letI := finiteGaussianPositiveMaximumLaw_isProbabilityMeasure S J hJ σ m
  letI := finiteGaussianAbsMaximumLaw_isProbabilityMeasure T J hJ
  unfold finiteGaussianMaximumResidualLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The enlarged Gaussian is independent of the actual sum of maxima, with exact marginal laws. -/
theorem gaussian_regression_maxima_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m v C : ℝ) :
    MeasurePreserving
      (fun p : EuclideanSpace ℝ ι × (ℝ × EuclideanSpace ℝ ι) ↦
        ((1 + C / v) * p.2.1, finiteGaussianPositiveMaximum J hJ σ m p.1 +
          finiteGaussianAbsMaximum J hJ p.2.2))
      ((multivariateGaussian (0 : EuclideanSpace ℝ ι) S).prod
        ((gaussianReal 0 v.toNNReal).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)))
      ((gaussianReal 0 ((1 + C / v) ^ 2 * v).toNNReal).prod
        (finiteGaussianMaximumResidualLaw S T J hJ σ m)) := by
  letI := finiteGaussianPositiveMaximumLaw_isProbabilityMeasure S J hJ σ m
  letI := finiteGaussianAbsMaximumLaw_isProbabilityMeasure T J hJ
  have hF : MeasurePreserving (finiteGaussianPositiveMaximum J hJ σ m)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S)
      (finiteGaussianPositiveMaximumLaw S J hJ σ m) :=
    ⟨(continuous_finiteGaussianPositiveMaximum J hJ σ m).measurable, rfl⟩
  have hR : MeasurePreserving (finiteGaussianAbsMaximum J hJ)
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) T)
      (finiteGaussianAbsMaximumLaw T J hJ) :=
    ⟨(continuous_finiteGaussianAbsMaximum J hJ).measurable, rfl⟩
  have hSum : MeasurePreserving (fun p : ℝ × ℝ ↦ p.1 + p.2)
      ((finiteGaussianPositiveMaximumLaw S J hJ σ m).prod
        (finiteGaussianAbsMaximumLaw T J hJ))
      (finiteGaussianMaximumResidualLaw S T J hJ σ m) := ⟨by fun_prop, rfl⟩
  exact ((gaussian_regression_scale_preserving v C).prod (hSum.comp (hF.prod hR))).comp
    (product_reference_first _ _ _)

end SRWTightness
