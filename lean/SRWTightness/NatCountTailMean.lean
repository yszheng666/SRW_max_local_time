import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- A natural count is exactly the sum of its positive tail indicators. -/
theorem nat_count_tail_series (N : ℕ) :
    (N : ℝ≥0∞) = ∑' n : ℕ, if n < N then (1 : ℝ≥0∞) else 0 := by
  classical
  symm
  calc
    _ = ∑ n ∈ Finset.range N, if n < N then (1 : ℝ≥0∞) else 0 := by
      apply tsum_eq_sum
      intro n hn
      exact if_neg (by simpa only [Finset.mem_range] using hn)
    _ = ∑ n ∈ Finset.range N, (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun n hn ↦ if_pos (Finset.mem_range.mp hn))
    _ = _ := by simp

/-- The nonnegative mean of a measurable natural count is the sum of its tail measures. -/
theorem lintegral_nat_count_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (hN : Measurable N) :
    (∫⁻ ω, (N ω : ℝ≥0∞) ∂μ) = ∑' n : ℕ, μ {ω | n + 1 ≤ N ω} := by
  classical
  have hS (n : ℕ) : MeasurableSet {ω | n < N ω} := measurableSet_lt measurable_const hN
  calc
    _ = ∫⁻ ω, ∑' n : ℕ, ({ω | n < N ω} : Set Ω).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂μ := by
      apply lintegral_congr
      intro ω
      simpa only [Set.indicator, Set.mem_setOf_eq] using nat_count_tail_series (N ω)
    _ = ∑' n : ℕ, ∫⁻ ω,
        ({ω | n < N ω} : Set Ω).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂μ :=
      lintegral_tsum (fun n ↦ (measurable_const.indicator (hS n)).aemeasurable)
    _ = ∑' n : ℕ, μ {ω | n < N ω} := by
      apply tsum_congr
      intro n
      rw [lintegral_indicator_const (hS n)]
      simp
    _ = _ := by
      apply tsum_congr
      intro n
      congr 1

/-- An integrable natural count has a summable real tail series equal to its ordinary mean. -/
theorem nat_count_mean_tail_series {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (hN : Measurable N) (hi : Integrable (fun ω ↦ (N ω : ℝ)) μ) :
    Summable (fun n : ℕ ↦ μ.real {ω | n + 1 ≤ N ω}) ∧
      (∫ ω, (N ω : ℝ) ∂μ) = ∑' n : ℕ, μ.real {ω | n + 1 ≤ N ω} := by
  have hmean : 0 ≤ ∫ ω, (N ω : ℝ) ∂μ := integral_nonneg (fun ω ↦ Nat.cast_nonneg _)
  have he : ENNReal.ofReal (∫ ω, (N ω : ℝ) ∂μ) =
      ∑' n : ℕ, μ {ω | n + 1 ≤ N ω} := by
    rw [ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun ω ↦ Nat.cast_nonneg _))]
    simpa only [ENNReal.ofReal_natCast] using lintegral_nat_count_tail μ N hN
  have hf : (∑' n : ℕ, μ {ω | n + 1 ≤ N ω}) ≠ ∞ := by
    rw [← he]
    exact ENNReal.ofReal_ne_top
  refine ⟨ENNReal.summable_toReal hf, ?_⟩
  calc
    _ = (ENNReal.ofReal (∫ ω, (N ω : ℝ) ∂μ)).toReal := (ENNReal.toReal_ofReal hmean).symm
    _ = (∑' n : ℕ, μ {ω | n + 1 ≤ N ω}).toReal := congrArg ENNReal.toReal he
    _ = _ := ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hf)

end SRWTightness
