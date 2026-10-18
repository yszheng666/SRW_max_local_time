import SRWTightness.ExponentialMoments
import SRWTightness.OneSidedMoment

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

private theorem integrable_exp_identity : Integrable (fun t : ℝ ↦ t) (expMeasure 1) := by
  simpa only [pow_one] using integrable_exponential_power 1

private theorem integral_exp_identity : (∫ t : ℝ, t ∂expMeasure 1) = 1 := by
  simpa only [pow_one, Nat.factorial_one, Nat.cast_one] using integral_exponential_power 1


 theorem integrable_exponential_centered :
    Integrable (fun n : ℝ ↦ n - 1) (expMeasure 1) :=
  (integrable_exp_identity).sub (integrable_const _)

 theorem integral_exponential_centered :
    (∫ n : ℝ, n - 1 ∂expMeasure 1) = 0 := by
  rw [integral_sub (integrable_exp_identity) (integrable_const _),
    integral_exp_identity, integral_const]
  simp

 theorem integrable_exponential_centered_two :
    Integrable (fun n : ℝ ↦ (n - 1) ^ 2) (expMeasure 1) := by
  have he : (fun n : ℝ ↦ (n - 1) ^ 2) =
      fun n : ℝ ↦ n ^ 2 - 2 * (1 : ℝ) * n + (1 : ℝ) ^ 2 := by funext n; ring
  rw [he]
  exact ((integrable_exponential_power 2).sub
    ((integrable_exp_identity).const_mul _)).add (integrable_const _)

 theorem integral_exponential_centered_two :
    (∫ n : ℝ, (n - 1) ^ 2 ∂expMeasure 1) = 1 := by
  have he : (fun n : ℝ ↦ (n - 1) ^ 2) =
      fun n : ℝ ↦ n ^ 2 - 2 * (1 : ℝ) * n + (1 : ℝ) ^ 2 := by funext n; ring
  have h21 : Integrable (fun n : ℝ ↦ n ^ 2 - 2 * (1 : ℝ) * n)
      (expMeasure 1) := (integrable_exponential_power 2).sub
        ((integrable_exp_identity).const_mul _)
  rw [he, integral_add h21 (integrable_const _),
    integral_sub (integrable_exponential_power 2) ((integrable_exp_identity).const_mul _),
    integral_const_mul, integral_exponential_power, integral_exp_identity, integral_const]
  norm_num [integral_const_mul, integral_exp_identity]

 theorem integrable_exponential_centered_four :
    Integrable (fun n : ℝ ↦ (n - 1) ^ 4) (expMeasure 1) := by
  have he : (fun n : ℝ ↦ (n - 1) ^ 4) =
      fun n : ℝ ↦ n ^ 4 - 4 * (1 : ℝ) * n ^ 3 +
        6 * (1 : ℝ) ^ 2 * n ^ 2 - 4 * (1 : ℝ) ^ 3 * n + (1 : ℝ) ^ 4 := by
    funext n; ring
  rw [he]
  exact ((((integrable_exponential_power 4).sub
    ((integrable_exponential_power 3).const_mul _)).add
    ((integrable_exponential_power 2).const_mul _)).sub
    ((integrable_exp_identity).const_mul _)).add (integrable_const _)

 theorem integral_exponential_centered_four :
    (∫ n : ℝ, (n - 1) ^ 4 ∂expMeasure 1) = 9 := by
  have he : (fun n : ℝ ↦ (n - 1) ^ 4) =
      fun n : ℝ ↦ n ^ 4 - 4 * (1 : ℝ) * n ^ 3 +
        6 * (1 : ℝ) ^ 2 * n ^ 2 - 4 * (1 : ℝ) ^ 3 * n + (1 : ℝ) ^ 4 := by
    funext n; ring
  have h43 : Integrable (fun n : ℝ ↦ n ^ 4 - 4 * (1 : ℝ) * n ^ 3)
      (expMeasure 1) := (integrable_exponential_power 4).sub
        ((integrable_exponential_power 3).const_mul _)
  have h432 : Integrable (fun n : ℝ ↦ n ^ 4 - 4 * (1 : ℝ) * n ^ 3 +
      6 * (1 : ℝ) ^ 2 * n ^ 2) (expMeasure 1) :=
    h43.add ((integrable_exponential_power 2).const_mul _)
  have h4321 : Integrable (fun n : ℝ ↦ n ^ 4 - 4 * (1 : ℝ) * n ^ 3 +
      6 * (1 : ℝ) ^ 2 * n ^ 2 - 4 * (1 : ℝ) ^ 3 * n) (expMeasure 1) :=
    h432.sub ((integrable_exp_identity).const_mul _)
  rw [he, integral_add h4321 (integrable_const _),
    integral_sub h432 ((integrable_exp_identity).const_mul _),
    integral_add h43 ((integrable_exponential_power 2).const_mul _),
    integral_sub (integrable_exponential_power 4) ((integrable_exponential_power 3).const_mul _)]
  simp only [integral_const_mul, integral_exponential_power, integral_exponential_power,
    integral_exponential_power, integral_exp_identity, integral_const,
    measureReal_univ_eq_one, one_smul]
  norm_num
  rw [integral_const_mul (4 : ℝ) (fun a : ℝ ↦ a), integral_exp_identity]
  norm_num

end SRWTightness
