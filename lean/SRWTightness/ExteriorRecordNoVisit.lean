import SRWTightness.ExteriorPathRecord
import SRWTightness.PathWordDirectionsSlice
import SRWTightness.ChildWordEmpty

namespace SRWTightness

/-- With no inner visit, the complete exterior record is the unchanged original word. -/
theorem wordExteriorRecord_no_visit (K C : Finset Site) (label : Site → Bool)
    (x : Site) (w : PathWord)
    (hvisit : ∀ i ≤ w.length, x + position (wordPath w) i ∉ K) :
    wordExteriorRecord K C label x w = ([], w) := by
  have hh := scanChildIntervals_skip_prefix K C x (wordPath w)
    (List.range (w.length + 1)) []
    (fun i hi ↦ hvisit i (by simpa using List.mem_range.mp hi))
  have he : wordChildIntervals K C x w = [] := by
    simpa only [List.append_nil, scanChildIntervals, wordChildIntervals] using hh
  simp only [wordExteriorRecord, he, packExteriorRecord, slicePathWord_full]

end SRWTightness
