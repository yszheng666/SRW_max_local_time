import SRWTightness.KilledWordFlatten
import SRWTightness.WordMark

namespace SRWTightness

/-- Complete short roots split exactly over the complete containing parent words. -/
theorem word_child_root_count_sum (hF : TwoLevelWordFlatteningInput)
    (K C L E : Finset Site) (hKC : K ⊆ C) (hLE : L ⊆ E)
    (hLK : L ⊆ K) (hEC : E ⊆ C) (x : Site) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ C) :
    (wordChildRecords K C x
      (fun y u ↦ wordMarkRootCount L E (some (y, u))) w).sum =
      (wordChildIntervals L E x w).length := by
  have hh := congrArg List.length
    (word_child_records_flatten hF K C L E hKC hLE hLK hEC x w hend
      (fun y u ↦ (y, u)))
  simpa only [List.length_flatten, wordChildRecords, List.map_map,
    Function.comp_def, List.length_map, wordMarkRootCount] using hh

/-- The original killed walk's short-root count is the sum over its complete parent words. -/
theorem killed_child_root_count_sum (hF : TwoLevelWordFlatteningInput)
    (D K C L E : Finset Site) (hKC : K ⊆ C) (hLE : L ⊆ E)
    (hLK : L ⊆ K) (hEC : E ⊆ C) (hCD : C ⊆ D) (x : Site)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    (killedChildRecords D K C x
      (fun y u ↦ wordMarkRootCount L E (some (y, u))) ω).sum =
      (killedChildIntervals D L E x ω).length :=
  word_child_root_count_sum hF K C L E hKC hLE hLK hEC x (killedPathWord D x ω)
    (killedPathWord_endpoint_outside_child D C hCD x ω hfin)

end SRWTightness
