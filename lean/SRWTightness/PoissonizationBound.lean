import SRWTightness.PoissonOneSided

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

/-- A monotone event probability loses at most a factor 16 under Poissonization. -/
theorem monotone_poissonization_bound (p : ℕ → ℝ) (hp0 : ∀ n, 0 ≤ p n)
    (hp1 : ∀ n, p n ≤ 1) (hmono : Monotone p) (k : ℕ) (hk : 1 ≤ k) :
    p k ≤ 16 * ∫ n : ℕ, p n ∂poissonMeasure (k : ℝ≥0) := by
  let μ := poissonMeasure (k : ℝ≥0)
  let S := {n : ℕ | k ≤ n}
  have hS : MeasurableSet S := MeasurableSet.of_discrete
  have hI : Integrable p μ := ⟨(measurable_of_countable p).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) (Filter.Eventually.of_forall (fun n ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 n)]
      exact hp1 n))⟩
  have hi : Integrable (S.indicator (fun _ : ℕ ↦ p k)) μ :=
    (integrable_const _).indicator hS
  have hpoint (n : ℕ) : S.indicator (fun _ : ℕ ↦ p k) n ≤ p n := by
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn]
      exact hmono hn
    · rw [Set.indicator_of_notMem hn]
      exact hp0 n
  have hb := integral_mono hi hI hpoint
  rw [integral_indicator_const _ hS, smul_eq_mul] at hb
  have hl := mul_le_mul_of_nonneg_right (poisson_probability_ge_mean k hk) (hp0 k)
  change (1 / 16 : ℝ) * p k ≤ μ.real S * p k at hl
  change p k ≤ 16 * ∫ n : ℕ, p n ∂μ
  linarith

end SRWTightness
