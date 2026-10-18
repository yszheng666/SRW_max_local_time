import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Matrix WithLp
namespace SRWTightness

/-- Covariance remaining after regression on one nondegenerate coordinate. -/
noncomputable def finiteGaussianRegressionCov {ι : Type*} (S : Matrix ι ι ℝ) (o : ι) :
    Matrix ι ι ℝ := fun x y ↦ S x y - S x o * S y o / S o o

/-- Reconstruct the field from an independent reference coordinate and residual vector. -/
noncomputable def finiteGaussianRegressionRebuild {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) (p : ℝ × EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun x ↦ S x o / S o o * p.1 + p.2 x)

/-- Standard finite Gaussian regression, stated for arbitrary covariance matrices. -/
def FiniteGaussianRegressionInput : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (o : ι),
    S.PosSemidef → 0 < S o o →
    (finiteGaussianRegressionCov S o).PosSemidef ∧
    ((gaussianReal 0 (S o o).toNNReal).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) (finiteGaussianRegressionCov S o))).map
        (finiteGaussianRegressionRebuild S o) =
      multivariateGaussian (0 : EuclideanSpace ℝ ι) S

end SRWTightness
