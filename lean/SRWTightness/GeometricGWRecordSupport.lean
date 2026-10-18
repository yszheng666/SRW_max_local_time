import SRWTightness.GeometricGWOneGeneration

open MeasureTheory
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- The actual finite GW record law is supported on records of its exact horizon length. -/
theorem geometric_gw_record_wrong_length_zero (k n : ℕ) :
    geometricGWRecordLaw k n {r | r.length ≠ n + 1} = 0 := by
  induction n with
  | zero => simp [geometricGWRecordLaw, Measure.dirac_apply]
  | succ n ih =>
    rw [geometricGWRecordLaw, Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable _).aemeasurable]
    apply lintegral_eq_zero_of_ae_eq_zero
    have hh : ∀ᵐ r ∂geometricGWRecordLaw k n, r.length = n + 1 := by
      exact ae_iff.mpr ih
    filter_upwards [hh] with r hr
    rw [geometricGWRecordStep, Measure.map_apply (measurable_of_countable _)
      (Set.to_countable _).measurableSet]
    have he : (fun j : ℕ ↦ j :: r) ⁻¹' {q | q.length ≠ n + 1 + 1} = ∅ := by
      ext j
      simp [hr]
    rw [he, measure_empty]
    rfl

/-- The original GW record has exactly one coordinate for each observed generation. -/
theorem geometric_gw_record_length_ae (k n : ℕ) :
    ∀ᵐ r ∂geometricGWRecordLaw k n, r.length = n + 1 := by
  exact ae_iff.mpr (geometric_gw_record_wrong_length_zero k n)

end SRWTightness
