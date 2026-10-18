import SRWTightness.ExteriorFiberProportionalLaw
import SRWTightness.CountableEventProportionalMass

open MeasureTheory
namespace SRWTightness

/-- The full original exterior bridge factorization input follows from actual finite path masses. -/
theorem exteriorBridgeFactorizationInput_internal : ExteriorBridgeFactorizationInput := by
  intro D K C label x hKC hCD h hh us hlen
  have he := exterior_atom_exit_positive_internal D K C hKC label x h hh
  let ν := exteriorIndependentWordLaw C C h
  letI : IsProbabilityMeasure ν := exteriorIndependentWordLaw_isProbabilityMeasure C C h
    (by intro slot hs; simpa only [ite_self] using he slot hs)
  have hA := exteriorBridgeNormalization_pos C h he
  have hnorm : pathLaw.real {ω | killedExteriorRecord D K C label x ω = h} =
      exteriorBridgeNormalization C h := by
    apply countable_event_proportional_mass pathLaw ν
      (killedChildRecords D K C x (fun _ u ↦ u))
      (measurable_killedChildRecords D K C x (fun _ u ↦ u)) _ _ hA.le
    intro vs
    exact exterior_fiber_proportional_law D K C label hKC hCD x h hh vs
  have hj := exterior_fiber_proportional_law D K C label hKC hCD x h hh us
  rw [hj, hnorm, mul_div_cancel_left₀ _ hA.ne']
  simpa only [labeledExteriorBridgeWordProduct, exteriorBridgeWordProduct, ite_self] using
    exteriorIndependentWordLaw_singleton C C h us hlen

end SRWTightness
