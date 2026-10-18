import SRWTightness.PoissonRawMoments

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem integrable_poisson_centered (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) - r) (poissonMeasure r) :=
  (integrable_poisson_power_one r).sub (integrable_const _)

 theorem integral_poisson_centered (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) - r ∂poissonMeasure r) = 0 := by
  rw [integral_sub (integrable_poisson_power_one r) (integrable_const _),
    integral_poisson_power_one, integral_const]
  simp

 theorem integrable_poisson_centered_two (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ ((n : ℝ) - r) ^ 2) (poissonMeasure r) := by
  have he : (fun n : ℕ ↦ ((n : ℝ) - r) ^ 2) =
      fun n : ℕ ↦ (n : ℝ) ^ 2 - 2 * (r : ℝ) * n + (r : ℝ) ^ 2 := by funext n; ring
  rw [he]
  exact ((integrable_poisson_power_two r).sub
    ((integrable_poisson_power_one r).const_mul _)).add (integrable_const _)

 theorem integral_poisson_centered_two (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r) ^ 2 ∂poissonMeasure r) = r := by
  have he : (fun n : ℕ ↦ ((n : ℝ) - r) ^ 2) =
      fun n : ℕ ↦ (n : ℝ) ^ 2 - 2 * (r : ℝ) * n + (r : ℝ) ^ 2 := by funext n; ring
  have h21 : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2 - 2 * (r : ℝ) * n)
      (poissonMeasure r) := (integrable_poisson_power_two r).sub
        ((integrable_poisson_power_one r).const_mul _)
  rw [he, integral_add h21 (integrable_const _),
    integral_sub (integrable_poisson_power_two r) ((integrable_poisson_power_one r).const_mul _),
    integral_const_mul, integral_poisson_power_two, integral_poisson_power_one, integral_const]
  simp
  <;> ring

 theorem integrable_poisson_centered_four (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ ((n : ℝ) - r) ^ 4) (poissonMeasure r) := by
  have he : (fun n : ℕ ↦ ((n : ℝ) - r) ^ 4) =
      fun n : ℕ ↦ (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3 +
        6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2 - 4 * (r : ℝ) ^ 3 * n + (r : ℝ) ^ 4 := by
    funext n; ring
  rw [he]
  exact ((((integrable_poisson_power_four r).sub
    ((integrable_poisson_power_three r).const_mul _)).add
    ((integrable_poisson_power_two r).const_mul _)).sub
    ((integrable_poisson_power_one r).const_mul _)).add (integrable_const _)

 theorem integral_poisson_centered_four (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r) ^ 4 ∂poissonMeasure r) = 3 * (r : ℝ) ^ 2 + r := by
  have he : (fun n : ℕ ↦ ((n : ℝ) - r) ^ 4) =
      fun n : ℕ ↦ (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3 +
        6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2 - 4 * (r : ℝ) ^ 3 * n + (r : ℝ) ^ 4 := by
    funext n; ring
  have h43 : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3)
      (poissonMeasure r) := (integrable_poisson_power_four r).sub
        ((integrable_poisson_power_three r).const_mul _)
  have h432 : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3 +
      6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2) (poissonMeasure r) :=
    h43.add ((integrable_poisson_power_two r).const_mul _)
  have h4321 : Integrable (fun n : ℕ ↦ (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3 +
      6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2 - 4 * (r : ℝ) ^ 3 * n) (poissonMeasure r) :=
    h432.sub ((integrable_poisson_power_one r).const_mul _)
  rw [he, integral_add h4321 (integrable_const _),
    integral_sub h432 ((integrable_poisson_power_one r).const_mul _),
    integral_add h43 ((integrable_poisson_power_two r).const_mul _),
    integral_sub (integrable_poisson_power_four r) ((integrable_poisson_power_three r).const_mul _)]
  simp only [integral_const_mul, integral_poisson_power_four, integral_poisson_power_three,
    integral_poisson_power_two, integral_poisson_power_one, integral_const,
    measureReal_univ_eq_one, one_smul]
  ring

end SRWTightness
