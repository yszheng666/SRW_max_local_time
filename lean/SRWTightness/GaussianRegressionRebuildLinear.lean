import SRWTightness.ExternalGaussianRegression
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory ProbabilityTheory Matrix WithLp
namespace SRWTightness

/-- The original Gaussian reconstruction formula as a real linear map. -/
noncomputable def finiteGaussianRegressionRebuildLinear {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) : (ℝ × EuclideanSpace ℝ ι) →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := finiteGaussianRegressionRebuild S o
  map_add' p q := by
    ext i
    simp [finiteGaussianRegressionRebuild]
    ring
  map_smul' c p := by
    ext i
    simp [finiteGaussianRegressionRebuild, smul_eq_mul]
    ring

/-- The finite-dimensional reconstruction is a continuous linear map. -/
noncomputable def finiteGaussianRegressionRebuildCLM {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) : (ℝ × EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ ι :=
  (finiteGaussianRegressionRebuildLinear S o).toContinuousLinearMap

/-- Reconstruction is measurable on the exact scalar-times-residual product space. -/
theorem finite_gaussian_regression_rebuild_measurable {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) : Measurable (finiteGaussianRegressionRebuild S o) :=
  (finiteGaussianRegressionRebuildCLM S o).continuous.measurable

/-- The actual independent scalar/residual reconstruction has a Gaussian distribution. -/
theorem finite_gaussian_regression_rebuild_isGaussian {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) (o : ι) :
    IsGaussian (((gaussianReal 0 (S o o).toNNReal).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o))).map
        (finiteGaussianRegressionRebuild S o)) := by
  change IsGaussian (((gaussianReal 0 (S o o).toNNReal).prod
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o))).map
      (finiteGaussianRegressionRebuildCLM S o))
  infer_instance

end SRWTightness
