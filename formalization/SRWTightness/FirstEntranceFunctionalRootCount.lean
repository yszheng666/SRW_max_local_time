import SRWTightness.FirstEntranceWordFunctional
import SRWTightness.FirstEntranceRootPreservation

namespace SRWTightness

/-- Finite-word first-entry extraction preserves the complete short-root count of a killed path. -/
theorem firstEntranceWordOfWord_root_count (D K L C : Finset Site) (hLK : L ⊆ K)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    wordMarkRootCount L C (firstEntranceWordOfWord D K x (killedPathWord D x ω)) =
      (killedChildIntervals D L C x ω).length := by
  rw [firstEntranceWordOfWord_killedPathWord D K x ω hfin]
  exact (firstEntranceWordMark_root_count D K L C hLK x ω hfin).symm

end SRWTightness
