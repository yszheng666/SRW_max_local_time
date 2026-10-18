import SRWTightness.FiniteRecordReferenceMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- The branching-weight sum is exactly the nonnegative functional under the reference tree law. -/
theorem finite_record_reference_functional {M : Type*} [MeasurableSpace M] [Countable M]
    (μ : Measure M) (n : ℕ) [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    (g : FiniteExcursionRecord M n → ℝ≥0∞) :
    (∫⁻ r, g r ∂finiteRecordReferenceMeasure μ n) =
      ∑' r, g r * ENNReal.ofReal (finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r) := by
  letI := finiteExcursionRecord_countable M n
  rw [lintegral_countable']
  apply tsum_congr
  intro r
  rw [finiteRecordReferenceMeasure_apply, finiteRecordReferenceMass_singleton]

end SRWTightness
