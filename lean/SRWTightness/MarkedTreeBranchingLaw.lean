import SRWTightness.MarkedTreeNormalization

open MeasureTheory
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.FiniteExcursionRecord

namespace SRWTightness

/-- Depth zero has exactly the given independent terminal-mark law. -/
theorem finite_record_reference_measure_zero {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ] :
    finiteRecordReferenceMeasure μ 0 = μ := by
  change Measure.sum (fun x : M ↦ ENNReal.ofReal (μ.real {x}) • Measure.dirac x) = μ
  simp only [ofReal_measureReal (measure_ne_top μ _)]
  exact Measure.sum_smul_dirac μ

/-- Every reference parent samples a geometric child count and independent ordered child trees. -/
theorem finite_record_reference_measure_successor {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ]
    (n : ℕ) [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    [MeasurableSpace (List (FiniteExcursionRecord M n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord M n))] :
    finiteRecordReferenceMeasure μ (n + 1) =
      geometricMarkedListLaw (finiteRecordReferenceMeasure μ n) := by
  letI := finiteExcursionRecord_countable M n
  letI := finite_record_reference_measure_probability_internal μ n
  apply Measure.ext_of_singleton
  intro rs
  rw [finiteRecordReferenceMeasure_apply, finiteRecordReferenceMass_singleton,
    geometricMarkedListLaw_singleton]
  simp only [finiteRecordReferenceMeasure_real_singleton]
  rfl

end SRWTightness
