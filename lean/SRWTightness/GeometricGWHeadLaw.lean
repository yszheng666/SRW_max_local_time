import SRWTightness.GeometricGWRecordSupport
import SRWTightness.MeasureBindMap

open MeasureTheory

set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- The most recent population under the original finite geometric GW record law. -/
noncomputable def geometricGWHeadLaw (k n : ℕ) : Measure ℕ :=
  (geometricGWRecordLaw k n).map (fun r ↦ r.headD 0)

instance geometricGWHeadLaw_isProbabilityMeasure (k n : ℕ) :
    IsProbabilityMeasure (geometricGWHeadLaw k n) := by
  unfold geometricGWHeadLaw
  letI : IsProbabilityMeasure (geometricGWRecordLaw k n) :=
    geometricGWRecordLaw_isProbabilityMeasure k n
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- At zero generations the population law is the deterministic initial count. -/
theorem geometric_gw_head_law_zero (k : ℕ) :
    geometricGWHeadLaw k 0 = Measure.dirac k := by
  simp [geometricGWHeadLaw, geometricGWRecordLaw, Measure.map_dirac]

/-- The actual head population evolves by binding the original independent generation law. -/
theorem geometric_gw_head_law_step (k n : ℕ) :
    geometricGWHeadLaw k (n + 1) = (geometricGWHeadLaw k n).bind geometricGWGenerationLaw := by
  change ((geometricGWRecordLaw k n).bind geometricGWRecordStep).map (fun r ↦ r.headD 0) =
    ((geometricGWRecordLaw k n).map (fun r ↦ r.headD 0)).bind geometricGWGenerationLaw
  rw [measure_bind_map_output _ _ _ (measurable_of_countable _) (measurable_of_countable _),
    measure_map_bind_input _ _ _ (measurable_of_countable _) (measurable_of_countable _)]
  congr 1
  funext r
  unfold geometricGWRecordStep
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  simp only [Function.comp_def, List.headD_cons]
  change (geometricGWGenerationLaw (r.headD 0)).map id = _
  exact Measure.map_id

/-- On a record of the exact horizon length, the final chronological population is its head. -/
theorem geometric_gw_population_final_eq_head (r : GeometricGWRecord) (n : ℕ)
    (hr : r.length = n + 1) : geometricGWPopulation r n = r.headD 0 := by
  unfold geometricGWPopulation
  rw [List.getElem?_reverse' (l := r) (i := n) (j := 0)
    (show n + 0 + 1 = r.length by omega)]
  cases r <;> rfl

/-- The actual final chronological population has the same measure as the record head. -/
theorem geometric_gw_final_population_law (k n : ℕ) :
    (geometricGWRecordLaw k n).map (fun r ↦ geometricGWPopulation r n) =
      geometricGWHeadLaw k n := by
  apply Measure.map_congr
  filter_upwards [geometric_gw_record_length_ae k n] with r hr
  exact geometric_gw_population_final_eq_head r n hr

end SRWTightness
