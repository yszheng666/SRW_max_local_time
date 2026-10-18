import SRWTightness.GeometricGWLaw

open MeasureTheory
open scoped BigOperators

set_option allowUnsafeReducibility true in
attribute [local reducible] SRWTightness.GeometricGWRecord

namespace SRWTightness

local instance geometricGWOneNatListMeasurable :
    MeasurableSpace (List ℕ) := ⊤
local instance geometricGWOneNatListSingleton :
    MeasurableSingletonClass (List ℕ) := ⟨fun _ ↦ trivial⟩

/-- One initial individual has exactly the original critical geometric offspring law. -/
theorem geometric_gw_generation_one : geometricGWGenerationLaw 1 = geometricGWOffspringLaw := by
  unfold geometricGWGenerationLaw
  have hf : (fun ξ : Fin 1 → ℕ ↦ ∑ i, ξ i) = Function.eval (0 : Fin 1) := by
    funext ξ
    simp
  rw [hf]
  exact (measurePreserving_eval (fun _ : Fin 1 ↦ geometricGWOffspringLaw) 0).map_eq

/-- The first population record of a single root is the geometric count followed by that root. -/
theorem geometric_gw_record_one_generation :
    geometricGWRecordLaw 1 1 = geometricGWOffspringLaw.map
      (fun j ↦ (j :: [1] : GeometricGWRecord)) := by
  change (Measure.dirac (α := GeometricGWRecord) [1]).bind geometricGWRecordStep = _
  rw [Measure.dirac_bind (measurable_of_countable _) [1]]
  unfold geometricGWRecordStep
  simp only [List.headD_cons]
  rw [geometric_gw_generation_one]

end SRWTightness
