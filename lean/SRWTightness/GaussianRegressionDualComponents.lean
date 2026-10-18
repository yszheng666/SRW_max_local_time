import SRWTightness.GaussianRegressionRebuildLinear

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace SRWTightness

/-- The reference scalar coefficient seen by a characteristic-function test vector. -/
noncomputable def finiteGaussianRegressionDualCoefficient {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) (u : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, u i * (S i o / S o o)

/-- A zero reference scalar leaves the residual vector unchanged. -/
theorem finite_gaussian_regression_rebuild_zero_scalar {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) (v : EuclideanSpace ℝ ι) :
    finiteGaussianRegressionRebuild S o (0, v) = v := by
  ext i
  simp [finiteGaussianRegressionRebuild]

/-- The scalar component of the reconstruction dual is its explicit finite coefficient. -/
theorem finite_gaussian_regression_dual_inl {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) (u : EuclideanSpace ℝ ι) :
    ((InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u).comp
      (finiteGaussianRegressionRebuildCLM S o)).comp
        (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ ι)) =
      finiteGaussianRegressionDualCoefficient S o u • ContinuousLinearMap.id ℝ ℝ := by
  ext t
  simp [finiteGaussianRegressionRebuildCLM, finiteGaussianRegressionRebuildLinear,
    finiteGaussianRegressionRebuild, finiteGaussianRegressionDualCoefficient,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

/-- The residual component of the reconstruction dual is the original test vector. -/
theorem finite_gaussian_regression_dual_inr {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) (u : EuclideanSpace ℝ ι) :
    ((InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u).comp
      (finiteGaussianRegressionRebuildCLM S o)).comp
        (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ ι)) =
      InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u := by
  ext v
  change (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u)
    (finiteGaussianRegressionRebuild S o (0, v)) = _
  rw [finite_gaussian_regression_rebuild_zero_scalar]

end SRWTightness
