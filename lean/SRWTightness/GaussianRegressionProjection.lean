import SRWTightness.ExternalGaussianRegression

open Matrix
open scoped BigOperators
namespace SRWTightness

/-- The linear matrix removing regression on the chosen reference coordinate. -/
noncomputable def finiteGaussianRegressionProjection {ι : Type*} [DecidableEq ι]
    (S : Matrix ι ι ℝ) (o : ι) : Matrix ι ι ℝ :=
  fun x y ↦ (if x = y then 1 else 0) - (if y = o then S x o / S o o else 0)

/-- Left multiplication by the regression projection subtracts its reference row. -/
theorem finite_gaussian_regression_projection_mul {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) (o x y : ι) :
    (finiteGaussianRegressionProjection S o * S) x y =
      S x y - S x o / S o o * S o y := by
  simp [Matrix.mul_apply, finiteGaussianRegressionProjection, sub_mul,
    Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- Regression covariance is the covariance obtained by the actual projection matrix. -/
theorem finite_gaussian_regression_cov_projection {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) (o : ι) (hS : S.PosSemidef)
    (ho : 0 < S o o) :
    finiteGaussianRegressionProjection S o * S *
      (finiteGaussianRegressionProjection S o)ᴴ = finiteGaussianRegressionCov S o := by
  ext x y
  have hz : (finiteGaussianRegressionProjection S o * S) x o = 0 := by
    rw [finite_gaussian_regression_projection_mul, div_mul_cancel₀ _ ho.ne']
    ring
  have hsym : S o y = S y o := by simpa using hS.isHermitian.apply y o
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change (∑ z, (finiteGaussianRegressionProjection S o * S) x z *
    ((if y = z then 1 else 0) - (if z = o then S y o / S o o else 0))) = _
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hz, zero_mul, sub_zero]
  rw [finite_gaussian_regression_projection_mul, hsym]
  unfold finiteGaussianRegressionCov
  ring

/-- Every nondegenerate positive semidefinite covariance has positive semidefinite residual. -/
theorem finite_gaussian_regression_cov_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) (o : ι) (hS : S.PosSemidef)
    (ho : 0 < S o o) : (finiteGaussianRegressionCov S o).PosSemidef := by
  rw [← finite_gaussian_regression_cov_projection S o hS ho]
  exact hS.mul_mul_conjTranspose_same (finiteGaussianRegressionProjection S o)

end SRWTightness
