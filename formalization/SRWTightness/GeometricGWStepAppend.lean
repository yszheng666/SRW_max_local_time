import SRWTightness.GeometricGWOneGeneration

open MeasureTheory
set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.GeometricGWRecord

namespace SRWTightness

attribute [local instance] geometricGWOneNatListMeasurable geometricGWOneNatListSingleton

/-- Appending an earlier initial population commutes with the actual GW step on nonempty records. -/
theorem geometric_gw_step_append (r : GeometricGWRecord) (k : ℕ) (hr : r ≠ []) :
    geometricGWRecordStep (r ++ [k]) =
      (geometricGWRecordStep r).map (fun q ↦ q ++ [k]) := by
  cases r with
  | nil => exact (hr rfl).elim
  | cons j r =>
    unfold geometricGWRecordStep
    simp only [List.cons_append, List.headD_cons]
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl

end SRWTightness
