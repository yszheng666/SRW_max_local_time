import SRWTightness.GaussianRegressionProjection
import SRWTightness.GaussianRegressionDualComponents
import SRWTightness.GaussianRegressionQuadratic

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators RealInnerProductSpace
namespace SRWTightness

/-- Independent reference scalar and residual have exactly the original field characteristic
function. -/
theorem finite_gaussian_regression_rebuild_charFun {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) (o : ι) (hS : S.PosSemidef)
    (ho : 0 < S o o) (u : EuclideanSpace ℝ ι) :
    charFun (((gaussianReal 0 (S o o).toNNReal).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o))).map
        (finiteGaussianRegressionRebuild S o)) u =
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) u := by
  have hR := finite_gaussian_regression_cov_posSemidef S o hS ho
  let q := finiteGaussianRegressionDualCoefficient S o u
  have hc : charFunDual (gaussianReal 0 (S o o).toNNReal)
      (q • ContinuousLinearMap.id ℝ ℝ) = charFun (gaussianReal 0 (S o o).toNNReal) q := by
    rw [← charFun_map_eq_charFunDual_smul (ContinuousLinearMap.id ℝ ℝ) q]
    change charFun ((gaussianReal 0 (S o o).toNNReal).map id) q = _
    rw [Measure.map_id]
  have hr : charFunDual
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o))
      (InnerProductSpace.toDualMap ℝ (EuclideanSpace ℝ ι) u) =
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ ι)
        (finiteGaussianRegressionCov S o)) u := charFun_eq_charFunDual_toDualMap u |>.symm
  change charFun (((gaussianReal 0 (S o o).toNNReal).prod
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o))).map
      (finiteGaussianRegressionRebuildCLM S o)) u = _
  rw [charFun_eq_charFunDual_toDualMap, charFunDual_map, charFunDual_prod,
    finite_gaussian_regression_dual_inl, finite_gaussian_regression_dual_inr]
  change charFunDual (gaussianReal 0 (S o o).toNNReal)
    (q • ContinuousLinearMap.id ℝ ℝ) * _ = _
  rw [hc, hr, charFun_gaussianReal,
    charFun_multivariateGaussian hR, charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, zero_sub,
    Real.coe_toNNReal _ ho.le]
  rw [← Complex.exp_add]
  congr 1
  have hquad := finite_gaussian_regression_quadratic S o ho.ne' u
  change S o o * q ^ 2 + u ⬝ᵥ (finiteGaussianRegressionCov S o) *ᵥ u =
    u ⬝ᵥ S *ᵥ u at hquad
  have hcomplex : (S o o : ℂ) * (q : ℂ) ^ 2 +
      ((u ⬝ᵥ (finiteGaussianRegressionCov S o) *ᵥ u : ℝ) : ℂ) =
      ((u ⬝ᵥ S *ᵥ u : ℝ) : ℂ) := by exact_mod_cast hquad
  rw [← hcomplex]
  ring

/-- The complete finite Gaussian regression interface is internally proved. -/
theorem finite_gaussian_regression_input_internal : FiniteGaussianRegressionInput := by
  intro ι inst₁ inst₂ S o hS ho
  refine ⟨finite_gaussian_regression_cov_posSemidef S o hS ho, ?_⟩
  apply Measure.ext_of_charFun
  ext u
  exact finite_gaussian_regression_rebuild_charFun S o hS ho u

end SRWTightness
