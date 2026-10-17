import SRWTightness.PoissonFactorialMoments
import Mathlib.Tactic.IntervalCases

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem poisson_power_falling_expansion (n : ℕ) :
    (n : ℝ) ^ 2 = (n.descFactorial 2 : ℝ) + (n.descFactorial 1 : ℝ) ∧
    (n : ℝ) ^ 3 = (n.descFactorial 3 : ℝ) + 3 * (n.descFactorial 2 : ℝ) +
      (n.descFactorial 1 : ℝ) ∧
    (n : ℝ) ^ 4 = (n.descFactorial 4 : ℝ) + 6 * (n.descFactorial 3 : ℝ) +
      7 * (n.descFactorial 2 : ℝ) + (n.descFactorial 1 : ℝ) := by
  by_cases hn : n < 3
  · interval_cases n <;> norm_num [Nat.descFactorial]
  · have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, Nat.mul_one,
      Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_one,
      Nat.cast_ofNat]
    constructor
    · ring
    constructor <;> ring

 theorem integrable_poisson_power_one (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure r) := by
  simpa only [Nat.descFactorial_one] using integrable_poisson_falling r 1

 theorem integral_poisson_power_one (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa only [Nat.descFactorial_one, pow_one] using integral_poisson_falling r 1

 theorem integrable_poisson_power_two (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (poissonMeasure r) := by
  simp_rw [(poisson_power_falling_expansion _).1]
  exact (integrable_poisson_falling r 2).add (integrable_poisson_falling r 1)

 theorem integral_poisson_power_two (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + r := by
  simp_rw [(poisson_power_falling_expansion _).1]
  rw [integral_add (integrable_poisson_falling r 2) (integrable_poisson_falling r 1)]
  simp only [integral_poisson_falling, pow_one]

 theorem integrable_poisson_power_three (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 3) (poissonMeasure r) := by
  simp_rw [(poisson_power_falling_expansion _).2.1]
  exact ((integrable_poisson_falling r 3).add
    ((integrable_poisson_falling r 2).const_mul 3)).add (integrable_poisson_falling r 1)

 theorem integral_poisson_power_three (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 3 ∂poissonMeasure r) = (r : ℝ) ^ 3 + 3 * (r : ℝ) ^ 2 + r := by
  simp_rw [(poisson_power_falling_expansion _).2.1]
  have h32 : Integrable (fun n : ℕ ↦ (n.descFactorial 3 : ℝ) +
      3 * (n.descFactorial 2 : ℝ)) (poissonMeasure r) :=
    (integrable_poisson_falling r 3).add ((integrable_poisson_falling r 2).const_mul 3)
  rw [integral_add h32 (integrable_poisson_falling r 1),
    integral_add (integrable_poisson_falling r 3) ((integrable_poisson_falling r 2).const_mul 3),
    integral_const_mul]
  simp only [integral_poisson_falling, pow_one]

 theorem integrable_poisson_power_four (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 4) (poissonMeasure r) := by
  simp_rw [(poisson_power_falling_expansion _).2.2]
  exact (((integrable_poisson_falling r 4).add
    ((integrable_poisson_falling r 3).const_mul 6)).add
    ((integrable_poisson_falling r 2).const_mul 7)).add (integrable_poisson_falling r 1)

 theorem integral_poisson_power_four (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 4 ∂poissonMeasure r) =
      (r : ℝ) ^ 4 + 6 * (r : ℝ) ^ 3 + 7 * (r : ℝ) ^ 2 + r := by
  simp_rw [(poisson_power_falling_expansion _).2.2]
  have h43 : Integrable (fun n : ℕ ↦ (n.descFactorial 4 : ℝ) +
      6 * (n.descFactorial 3 : ℝ)) (poissonMeasure r) :=
    (integrable_poisson_falling r 4).add ((integrable_poisson_falling r 3).const_mul 6)
  have h432 : Integrable (fun n : ℕ ↦ (n.descFactorial 4 : ℝ) +
      6 * (n.descFactorial 3 : ℝ) + 7 * (n.descFactorial 2 : ℝ)) (poissonMeasure r) :=
    h43.add ((integrable_poisson_falling r 2).const_mul 7)
  rw [integral_add h432 (integrable_poisson_falling r 1),
    integral_add h43 ((integrable_poisson_falling r 2).const_mul 7),
    integral_add (integrable_poisson_falling r 4) ((integrable_poisson_falling r 3).const_mul 6)]
  simp only [integral_const_mul, integral_poisson_falling, pow_one]

end SRWTightness
