import SRWTightness.GaussianCoefficientTail
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem gaussianCoefficient_hasLaw (i : GaussianCoefficientIndex) :
    HasLaw (fun ω : GaussianCoefficientSpace ↦ ω i) (gaussianReal 0 1)
      gaussianCoefficientLaw :=
  ⟨(measurable_pi_apply i).aemeasurable, gaussianCoefficient_map i⟩

theorem gaussianCoefficient_mean (i : GaussianCoefficientIndex) :
    (∫ ω, ω i ∂gaussianCoefficientLaw) = 0 := by
  rw [(gaussianCoefficient_hasLaw i).integral_eq, integral_id_gaussianReal]

theorem gaussianCoefficient_variance (i : GaussianCoefficientIndex) :
    Var[fun ω ↦ ω i; gaussianCoefficientLaw] = 1 := by
  rw [(gaussianCoefficient_hasLaw i).variance_eq, variance_id_gaussianReal]
  rfl

theorem gaussianCoefficient_covariance (i j : GaussianCoefficientIndex) :
    cov[fun ω ↦ ω i, fun ω ↦ ω j; gaussianCoefficientLaw] = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    rw [covariance_self (measurable_pi_apply i).aemeasurable, gaussianCoefficient_variance]
    simp
  · rw [if_neg h]
    exact (gaussianCoefficient_independent.indepFun h).covariance_eq_zero
      ((gaussianCoefficient_subgaussian i).memLp 2) ((gaussianCoefficient_subgaussian j).memLp 2)

theorem gaussianCoefficient_linear_covariance (I : Finset GaussianCoefficientIndex)
    (a b : GaussianCoefficientIndex → ℝ) :
    cov[fun ω ↦ ∑ i ∈ I, a i * ω i, fun ω ↦ ∑ i ∈ I, b i * ω i;
      gaussianCoefficientLaw] = ∑ i ∈ I, a i * b i := by
  classical
  rw [covariance_fun_sum_fun_sum'
    (fun i _ ↦ ((gaussianCoefficient_subgaussian i).memLp 2).const_mul (a i))
    (fun i _ ↦ ((gaussianCoefficient_subgaussian i).memLp 2).const_mul (b i))]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    gaussianCoefficient_covariance]
  simp [mul_ite, hi, mul_comm]

theorem gaussianCoefficient_linear_mean (I : Finset GaussianCoefficientIndex)
    (a : GaussianCoefficientIndex → ℝ) :
    (∫ ω, ∑ i ∈ I, a i * ω i ∂gaussianCoefficientLaw) = 0 := by
  rw [integral_finsetSum I (fun i _ ↦
    (gaussianCoefficient_subgaussian i).integrable.const_mul (a i))]
  simp [integral_const_mul, gaussianCoefficient_mean]

end SRWTightness
