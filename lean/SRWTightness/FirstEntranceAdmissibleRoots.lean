import SRWTightness.AdmissibleWordKilledIdentity
import SRWTightness.FirstEntranceFunctionalRootCount
import SRWTightness.ChildSliceAdmissible
import SRWTightness.WordRootCountFlatten

namespace SRWTightness

/-- First-entry trimming preserves short roots on every admissible finite exit word. -/
theorem firstEntranceWordOfWord_admissible_roots (C K L E : Finset Site) (hLK : L ⊆ K)
    (x e : Site) (w : PathWord) (hw : AdmissibleExitWord C x e w) :
    wordMarkRootCount L E (firstEntranceWordOfWord C K x w) =
      (wordChildIntervals L E x w).length := by
  have hh := firstEntranceWordMark_root_count C K L E hLK x (wordPath w)
    (admissibleExitWord_domainSteps C x e w hw).1
  change (wordChildIntervals L E x (killedPathWord C x (wordPath w))).length = _ at hh
  rw [admissibleExitWord_killedPathWord C x e w hw] at hh
  exact hh.symm

/-- Actual complete parent slices preserve the total short-root count after first-entry trimming. -/
theorem word_child_firstEntrance_root_count_sum (hF : TwoLevelWordFlatteningInput)
    (K C O L E : Finset Site) (hKC : K ⊆ C) (hLE : L ⊆ E)
    (hLK : L ⊆ K) (hLO : L ⊆ O) (hEC : E ⊆ C) (x : Site) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ C) :
    (wordChildRecords K C x
      (fun y u ↦ wordMarkRootCount L E (firstEntranceWordOfWord C O y u)) w).sum =
        (wordChildIntervals L E x w).length := by
  calc
    _ = (wordChildRecords K C x
        (fun y u ↦ wordMarkRootCount L E (some (y, u))) w).sum := by
      apply congrArg List.sum
      unfold wordChildRecords
      apply List.map_congr_left
      intro q hq
      exact firstEntranceWordOfWord_admissible_roots C O L E hLO _ _ _
        (wordChildIntervals_slice_admissible K C hKC x w q hq)
    _ = _ := word_child_root_count_sum hF K C L E hKC hLE hLK hEC x w hend

end SRWTightness
