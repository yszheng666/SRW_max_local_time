import SRWTightness.GeometricGWRecordSupport
import SRWTightness.GeometricGWStepAppend
import SRWTightness.MeasureBindMap

open MeasureTheory
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- Appending an earlier initial population commutes with evolution of the actual record law. -/
theorem geometric_gw_record_append_evolution (j n k : ℕ) :
    ((geometricGWRecordLaw j n).map (fun r ↦ r ++ [k])).bind geometricGWRecordStep =
      (geometricGWRecordLaw j (n + 1)).map (fun r ↦ r ++ [k]) := by
  change _ = ((geometricGWRecordLaw j n).bind geometricGWRecordStep).map
    (fun r ↦ r ++ [k])
  rw [measure_map_bind_input _ _ _ (measurable_of_countable _) (measurable_of_countable _),
    measure_bind_map_output _ _ _ (measurable_of_countable _) (measurable_of_countable _)]
  apply Measure.bind_congr_right
  filter_upwards [geometric_gw_record_length_ae j n] with r hr
  have hne : r ≠ [] := by
    intro he
    simp [he] at hr
  exact geometric_gw_step_append r k hne

/-- The actual GW record law samples its first generation before the remaining finite horizon. -/
theorem geometric_gw_record_first_generation (k n : ℕ) :
    geometricGWRecordLaw k (n + 1) =
      (geometricGWGenerationLaw k).bind (fun j ↦
        (geometricGWRecordLaw j n).map (fun r ↦ r ++ [k])) := by
  induction n with
  | zero =>
    change (Measure.dirac (α := GeometricGWRecord) [k]).bind geometricGWRecordStep =
      (geometricGWGenerationLaw k).bind (fun j ↦
        (Measure.dirac (α := GeometricGWRecord) [j]).map (fun r ↦ r ++ [k]))
    rw [Measure.dirac_bind (measurable_of_countable _) [k]]
    simp only [Measure.map_dirac' (measurable_of_countable _), List.cons_append, List.nil_append]
    rw [Measure.bind_dirac_eq_map _ (measurable_of_countable _)]
    unfold geometricGWRecordStep
    simp only [List.headD_cons]
  | succ n ih =>
    change (geometricGWRecordLaw k (n + 1)).bind geometricGWRecordStep = _
    rw [ih]
    have hf : Measurable (fun j : ℕ ↦
        (geometricGWRecordLaw j n).map (fun r ↦ r ++ [k])) := measurable_of_countable _
    rw [Measure.bind_bind hf.aemeasurable (measurable_of_countable _).aemeasurable]
    apply congrArg ((geometricGWGenerationLaw k).bind)
    funext j
    exact geometric_gw_record_append_evolution j n k

end SRWTightness
