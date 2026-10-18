import SRWTightness.PoissonCenteredMoments

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- Uniform loss for replacing k independent marks by a Poisson number of mean k. -/
theorem poisson_probability_ge_mean (k : ℕ) (hk : 1 ≤ k) :
    (1 / 16 : ℝ) ≤ (poissonMeasure (k : ℝ≥0)).real {n : ℕ | k ≤ n} := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < k := by linarith
  have h2 : 0 < ∫ n : ℕ, ((n : ℝ) - (k : ℝ≥0)) ^ 2 ∂poissonMeasure (k : ℝ≥0) := by
    rw [integral_poisson_centered_two]
    exact hp
  have h4 : 0 < ∫ n : ℕ, ((n : ℝ) - (k : ℝ≥0)) ^ 4 ∂poissonMeasure (k : ℝ≥0) := by
    rw [integral_poisson_centered_four]
    change 0 < 3 * (k : ℝ) ^ 2 + k
    positivity
  have hb := positive_probability_lower_of_centered (poissonMeasure (k : ℝ≥0))
    (fun n : ℕ ↦ (n : ℝ) - (k : ℝ≥0)) (measurable_of_countable _)
    (integrable_poisson_centered _) (integrable_poisson_centered_two _)
    (integrable_poisson_centered_four _) (integral_poisson_centered _) h2 h4
  rw [integral_poisson_centered_two, integral_poisson_centered_four] at hb
  have hl : (1 / 16 : ℝ) ≤ (k : ℝ) ^ 2 / (4 * (3 * (k : ℝ) ^ 2 + k)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  apply hl.trans (hb.trans ?_)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro n hn
  have he : (k : ℝ) < n := by simpa using hn
  exact le_of_lt (by exact_mod_cast he)

end SRWTightness
