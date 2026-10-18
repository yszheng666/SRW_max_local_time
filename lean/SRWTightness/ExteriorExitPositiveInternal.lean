import SRWTightness.AdmissibleWordExitPositive
import SRWTightness.ChildSliceAdmissible
import SRWTightness.ExteriorRecordSupport

open MeasureTheory
namespace SRWTightness

/-- Every retained header of a finite word has a reachable exit, without a factorization input. -/
theorem wordExteriorRecord_exit_positive (K C : Finset Site) (hKC : K ⊆ C)
    (label : Site → Bool) (x : Site) (w : PathWord) (slot : ExteriorSlot)
    (hs : slot ∈ (wordExteriorRecord K C label x w).1) :
    0 < traceExitProbability C slot.2.2.1 slot.2.2.2 := by
  obtain ⟨q, hq, _, ha, he⟩ := packExteriorRecord_slot label x w
    (wordChildIntervals K C x w) 0 slot hs
  rw [ha, he]
  exact admissibleExitWord_exit_positive C _ _ (slicePathWord w q.1 q.2)
    (wordChildIntervals_slice_admissible K C hKC x w q hq)

/-- Positive exterior atoms have reachable exits in every slot, independently of bridge
factorization. -/
theorem exterior_atom_exit_positive_internal (D K C : Finset Site) (hKC : K ⊆ C)
    (label : Site → Bool) (x : Site) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h}) :
    ∀ slot ∈ h.1, 0 < traceExitProbability C slot.2.2.1 slot.2.2.2 := by
  obtain ⟨ω, hω⟩ := nonempty_of_measureReal_ne_zero hh.ne'
  intro slot hs
  apply wordExteriorRecord_exit_positive K C hKC label x (killedPathWord D x ω) slot
  change slot ∈ (killedExteriorRecord D K C label x ω).1
  rw [show killedExteriorRecord D K C label x ω = h from hω]
  exact hs

end SRWTightness
