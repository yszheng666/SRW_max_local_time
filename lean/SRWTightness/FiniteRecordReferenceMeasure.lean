import SRWTightness.RecordReferenceEventMass

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The existing marked-tree weights as an atomic measure on actual finite record shapes. -/
noncomputable def finiteRecordReferenceMeasure {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (n : ℕ) [MeasurableSpace (FiniteExcursionRecord M n)] :
    Measure (FiniteExcursionRecord M n) :=
  Measure.sum (fun r ↦ ENNReal.ofReal
    (finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r) • Measure.dirac r)

/-- The measure agrees with the previously audited reference event mass on every record event. -/
theorem finiteRecordReferenceMeasure_apply {M : Type*} [MeasurableSpace M] [Countable M]
    (μ : Measure M) (n : ℕ) [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    (s : Set (FiniteExcursionRecord M n)) :
    finiteRecordReferenceMeasure μ n s = finiteRecordReferenceMass μ n s := by
  classical
  letI := finiteExcursionRecord_countable M n
  have hs := s.to_countable.measurableSet
  simp only [finiteRecordReferenceMeasure, Measure.sum_apply _ hs,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs, finiteRecordReferenceMass]
  apply tsum_congr
  intro r
  by_cases hr : r ∈ s <;> simp [Set.indicator_apply, hr]

/-- Normalization follows from the existing explicit standard marked-GW input. -/
theorem finiteRecordReferenceMeasure_probability {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (hinput : MarkedGWTreeInput M)
    (μ : Measure M) (hμ : IsProbabilityMeasure μ) (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)] :
    IsProbabilityMeasure (finiteRecordReferenceMeasure μ n) := by
  constructor
  rw [finiteRecordReferenceMeasure_apply]
  exact markedGWTree_mass_one hinput μ hμ n

/-- The real singleton probability is exactly the root weight used by the actual comparison. -/
theorem finiteRecordReferenceMeasure_real_singleton {M : Type*} [MeasurableSpace M]
    [Countable M] (μ : Measure M) (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)] (r : FiniteExcursionRecord M n) :
    (finiteRecordReferenceMeasure μ n).real {r} =
      finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r := by
  rw [measureReal_def, finiteRecordReferenceMeasure_apply]
  exact finiteRecordReferenceMass_singleton_toReal μ n r

end SRWTightness
