import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Binding a finite natural law to finite natural kernels gives the exact
countable atom mixture. -/
theorem countable_nat_bind_real_atom (μ : Measure ℕ) (ν : ℕ → Measure ℕ)
    [IsFiniteMeasure μ] [∀ k, IsFiniteMeasure (ν k)] (m : ℕ) :
    (μ.bind ν).real {m} = ∑' k : ℕ, μ.real {k} * (ν k).real {m} := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton m)
    (measurable_of_countable ν).aemeasurable, lintegral_countable',
    ENNReal.tsum_toReal_eq (fun k ↦ ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul, ← measureReal_def, mul_comm]

/-- The real atom mixture is summable when the natural laws and kernels are probabilities. -/
theorem countable_nat_bind_atom_summable (μ : Measure ℕ) (ν : ℕ → Measure ℕ)
    [IsProbabilityMeasure μ] [∀ k, IsProbabilityMeasure (ν k)] (m : ℕ) :
    Summable (fun k : ℕ ↦ μ.real {k} * (ν k).real {m}) := by
  letI : IsProbabilityMeasure (μ.bind ν) := isProbabilityMeasure_bind
    (measurable_of_countable ν).aemeasurable (Filter.Eventually.of_forall fun k ↦ inferInstance)
  have hB : (μ.bind ν) {m} = ∑' k : ℕ, ν k {m} * μ {k} := by
    rw [Measure.bind_apply (measurableSet_singleton m)
      (measurable_of_countable ν).aemeasurable, lintegral_countable']
  have hfinite := measure_ne_top (μ.bind ν) {m}
  rw [hB] at hfinite
  simpa only [ENNReal.toReal_mul, ← measureReal_def, mul_comm] using
    ENNReal.summable_toReal hfinite

end SRWTightness
