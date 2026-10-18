import SRWTightness.GaussianCenteredSubgaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace SRWTightness

/-- Every centered multivariate Gaussian coordinate has zero expectation. -/
theorem centered_multivariate_coordinate_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i : ι) :
    (∫ φ : EuclideanSpace ℝ ι, φ i ∂multivariateGaussian 0 S) = 0 := by
  have hh := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ ι)) hS (i := i)).hasLaw.integral_eq
  simpa using hh

/-- Actual coordinate differences obey the sub-Gaussian bound from their exact covariance. -/
theorem gaussian_coordinate_increment_subgaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i j : ι) (v : ℝ≥0)
    (hv : S i i + S j j - 2 * S i j ≤ v) :
    HasSubgaussianMGF (fun φ : EuclideanSpace ℝ ι ↦ φ i - φ j) v
      (multivariateGaussian 0 S) := by
  have hm (k : ι) : MemLp (fun φ : EuclideanSpace ℝ ι ↦ φ k) 2
      (multivariateGaussian 0 S) :=
    (measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ ι)) hS (i := k)).hasLaw.hasGaussianLaw.memLp_two
  have hG : HasGaussianLaw (fun φ : EuclideanSpace ℝ ι ↦ φ i - φ j)
      (multivariateGaussian 0 S) := by
    exact (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S)).map
      (EuclideanSpace.proj i - EuclideanSpace.proj j)
  refine gaussian_centered_subgaussian_bound _ _ hG ?_ v ?_
  · rw [integral_sub ((hm i).integrable (by norm_num)) ((hm j).integrable (by norm_num)),
      centered_multivariate_coordinate_mean S hS i, centered_multivariate_coordinate_mean S hS j]
    simp
  · have hh := variance_sub (hm i) (hm j)
    simp only [variance_eval_multivariateGaussian hS, covariance_eval_multivariateGaussian hS] at hh
    exact hh.trans_le (by linarith)

/-- A zero-variance coordinate of the actual centered Gaussian vector vanishes almost surely. -/
theorem centered_multivariate_zero_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (o : ι) (ho : S o o = 0) :
    ∀ᵐ φ : EuclideanSpace ℝ ι ∂multivariateGaussian 0 S, φ o = 0 := by
  have hG := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ ι)) hS (i := o)).hasLaw.hasGaussianLaw
  have hh := gaussian_centered_subgaussian_bound _ _ hG
    (centered_multivariate_coordinate_mean S hS o) 0
    (by rw [variance_eval_multivariateGaussian hS, ho]; simp)
  exact hh.ae_eq_zero_of_hasSubgaussianMGF_zero

/-- Zero increment variance identifies the two coordinates on a probability-one set. -/
theorem centered_multivariate_zero_increment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (i j : ι)
    (hij : S i i + S j j - 2 * S i j ≤ 0) :
    ∀ᵐ φ : EuclideanSpace ℝ ι ∂multivariateGaussian 0 S, φ i = φ j := by
  have hh :=
    (gaussian_coordinate_increment_subgaussian S hS i j 0 hij).ae_eq_zero_of_hasSubgaussianMGF_zero
  filter_upwards [hh] with φ hφ
  exact sub_eq_zero.mp hφ

end SRWTightness
