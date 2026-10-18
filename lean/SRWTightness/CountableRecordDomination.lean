import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- On a countable measurable record space, atom inequalities imply measure domination. -/
theorem countable_measure_le_of_singletons {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Countable R] (μ ν : Measure R)
    (h : ∀ r, μ {r} ≤ ν {r}) : μ ≤ ν := by
  classical
  apply Measure.le_iff.mpr
  intro S hS
  rw [← Measure.tsum_indicator_apply_singleton μ S hS,
    ← Measure.tsum_indicator_apply_singleton ν S hS]
  exact ENNReal.tsum_le_tsum (fun r ↦ by
    by_cases hr : r ∈ S <;> simp [Set.indicator_apply, hr, h])

/-- A record comparison restricted to its valid error region dominates that restricted measure. -/
theorem restricted_record_domination {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Countable R] (μ ν : Measure R) (G : Set R) (c : ℝ≥0∞)
    (h : ∀ r ∈ G, μ {r} ≤ c * ν {r}) : μ.restrict G ≤ c • ν := by
  classical
  apply countable_measure_le_of_singletons
  intro r
  rw [Measure.restrict_apply (measurableSet_singleton r), Measure.smul_apply, smul_eq_mul]
  by_cases hr : r ∈ G
  · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hr)]
    exact h r hr
  · have he : {r} ∩ G = ∅ := by ext x; simp only [Set.mem_inter_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false]; aesop
    rw [he, measure_empty]
    exact zero_le

/-- Independent auxiliary integration preserves the restricted record comparison. -/
theorem record_auxiliary_domination {R Ω : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Countable R] [MeasurableSpace Ω]
    (μ ν : Measure R) [SFinite μ] (σ : Measure Ω) [SFinite σ] (G : Set R) (c : ℝ≥0∞)
    (h : ∀ r ∈ G, μ {r} ≤ c * ν {r}) :
    (μ.prod σ).restrict (G ×ˢ Set.univ) ≤ c • (ν.prod σ) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, ← Measure.prod_smul_left]
  exact Measure.prod_mono (restricted_record_domination μ ν G c h) le_rfl

end SRWTightness
