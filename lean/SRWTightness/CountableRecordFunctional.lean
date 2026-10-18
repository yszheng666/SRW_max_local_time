import SRWTightness.KilledRecordEventComparison
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Countable record fiber bounds transfer to every nonnegative supported functional. -/
theorem countable_record_functional_comparison {Ω R : Type*} [MeasurableSpace Ω]
    [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
    (μ : Measure Ω) (f : Ω → R) (hf : Measurable f) (q g : R → ℝ≥0∞)
    (s : Set R) (hg : ∀ r, r ∉ s → g r = 0) (L U : ℝ≥0∞)
    (h : ∀ r ∈ s, L * q r ≤ μ (f ⁻¹' {r}) ∧ μ (f ⁻¹' {r}) ≤ U * q r) :
    L * (∑' r, g r * q r) ≤ ∫⁻ ω, g (f ω) ∂μ ∧
      (∫⁻ ω, g (f ω) ∂μ) ≤ U * (∑' r, g r * q r) := by
  have hid : (∫⁻ ω, g (f ω) ∂μ) = ∑' r, g r * μ (f ⁻¹' {r}) := by
    rw [show (fun ω ↦ g (f ω)) = g ∘ f from rfl,
      lintegral_comp (measurable_of_countable g) hf, lintegral_countable']
    congr 1
    funext r
    rw [Measure.map_apply hf (measurableSet_singleton r)]
  rw [hid, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  constructor
  · apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : r ∈ s
    · simpa only [mul_left_comm] using mul_le_mul_left' (h r hr).1 (g r)
    · simp [hg r hr]
  · apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : r ∈ s
    · simpa only [mul_left_comm] using mul_le_mul_left' (h r hr).2 (g r)
    · simp [hg r hr]

end SRWTightness
