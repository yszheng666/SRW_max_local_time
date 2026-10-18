import SRWTightness.OneSidedMoment
import Mathlib.Probability.Distributions.Poisson.Basic

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem poisson_falling_term_succ (r : ℝ≥0) (k n : ℕ) :
    Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) *
        ((n + 1).descFactorial (k + 1) : ℝ) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) *
        (n.descFactorial k : ℝ)) := by
  rw [Nat.succ_descFactorial_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

 theorem hasSum_poisson_falling (r : ℝ≥0) (k : ℕ) :
    HasSum (fun n : ℕ ↦ Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ) *
      (n.descFactorial k : ℝ)) ((r : ℝ) ^ k) := by
  induction k with
  | zero => simpa using hasSum_one_poissonMeasure r
  | succ k ih =>
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.zero_descFactorial_succ, Nat.cast_zero, mul_zero,
      sub_zero]
    simp_rw [poisson_falling_term_succ]
    simpa only [pow_succ, mul_comm ((r : ℝ) ^ k) (r : ℝ)] using ih.mul_left (r : ℝ)

 theorem integrable_poisson_falling (r : ℝ≥0) (k : ℕ) :
    Integrable (fun n : ℕ ↦ (n.descFactorial k : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [Real.norm_eq_abs, Nat.abs_cast]
    using (hasSum_poisson_falling r k).summable

 theorem integral_poisson_falling (r : ℝ≥0) (k : ℕ) :
    (∫ n : ℕ, (n.descFactorial k : ℝ) ∂poissonMeasure r) = (r : ℝ) ^ k := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (hasSum_poisson_falling r k).tsum_eq

end SRWTightness
