import SRWTightness.ExternalGaussianRegression
import SRWTightness.GaussianDomainDecomposition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory Matrix
namespace SRWTightness

/-- Regression uses the actual harmonic Green covariance, not a substituted Gaussian model. -/
theorem harmonic_gaussian_regression (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o : E)
    (hv : 0 < (observationGreen D E - greenMatrix E) o o) :
    (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o).PosSemidef ∧
    ((gaussianReal 0 ((observationGreen D E - greenMatrix E) o o).toNNReal).prod
      (multivariateGaussian (0 : EuclideanSpace ℝ E)
        (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o))).map
        (finiteGaussianRegressionRebuild (observationGreen D E - greenMatrix E) o) =
      harmonicGaussianLaw D E := by
  exact hReg E (observationGreen D E - greenMatrix E) o
    (green_difference_posSemidef D E hED) hv

/-- The regression residual has zero reference-coordinate variance. -/
theorem finite_gaussian_regression_anchor {ι : Type*} (S : Matrix ι ι ℝ) (o : ι)
    (hv : 0 < S o o) : finiteGaussianRegressionCov S o o o = 0 := by
  dsimp [finiteGaussianRegressionCov]
  field_simp
  <;> ring

/-- Regression can only decrease the variance of any field increment. -/
theorem finite_gaussian_regression_increment {ι : Type*} (S : Matrix ι ι ℝ)
    (o x y : ι) (hv : 0 < S o o) :
    finiteGaussianRegressionCov S o x x + finiteGaussianRegressionCov S o y y -
      2 * finiteGaussianRegressionCov S o x y ≤ S x x + S y y - 2 * S x y := by
  have he : finiteGaussianRegressionCov S o x x + finiteGaussianRegressionCov S o y y -
      2 * finiteGaussianRegressionCov S o x y = S x x + S y y - 2 * S x y -
        (S x o - S y o) ^ 2 / S o o := by
    dsimp [finiteGaussianRegressionCov]
    ring
  rw [he]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hv.le)

/-- The actual residual Gaussian covariance is the displayed Schur complement. -/
theorem harmonic_gaussian_regression_covariance (hReg : FiniteGaussianRegressionInput)
    (D E : Finset Site) (hED : E ⊆ D) (o x y : E)
    (hv : 0 < (observationGreen D E - greenMatrix E) o o) :
    covariance (fun φ : EuclideanSpace ℝ E ↦ φ x) (fun φ : EuclideanSpace ℝ E ↦ φ y)
      (multivariateGaussian (0 : EuclideanSpace ℝ E)
        (finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o)) =
      finiteGaussianRegressionCov (observationGreen D E - greenMatrix E) o x y := by
  exact covariance_eval_multivariateGaussian (harmonic_gaussian_regression hReg D E hED o hv).1
    x y

end SRWTightness
