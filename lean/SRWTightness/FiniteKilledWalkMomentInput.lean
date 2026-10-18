import SRWTightness.ActualChildRecords
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory
namespace SRWTightness

/-- Standard finite-domain SRW input: every square-root exponential of the exit duration is
integrable. It follows from the geometric exit tail and supplies no source-specific moment bound. -/
def FiniteKilledWalkMomentInput : Prop :=
  ∀ (D : Finset Site) (x : Site) (c : ℝ),
    Integrable (fun ω ↦ Real.exp (c * Real.sqrt ((domainSteps D x ω : ℝ) + 1))) pathLaw

/-- Direct chronological record extraction cannot emit more records than inspected times. -/
theorem killed_child_records_length_le {M : Type*} (D K C : Finset Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) :
    (killedChildRecords D K C x F ω).length ≤ domainSteps D x ω + 1 := by
  simpa only [killedChildRecords, wordChildRecords, List.length_map, wordChildIntervals,
    List.length_range, killedPathWord] using
    scanChildIntervals_length_le K C x (wordPath (killedPathWord D x ω))
      (List.range ((killedPathWord D x ω).length + 1)) none

end SRWTightness
