import SRWTightness.ChildSliceRecords
import SRWTightness.ChildScanNestedRange
import SRWTightness.ChildTimeBlock

namespace SRWTightness

/-- The actual nested records split at each complete parent block without losing order. -/
theorem wordChildRecords_nested_renewal {M : Type*} (K C K' C' : Finset Site)
    (hKC' : K' ⊆ C') (hK : K' ⊆ K) (hC : C' ⊆ C)
    (x : Site) (w : PathWord) (F : Site → PathWord → M) (a b : ℕ)
    (hab : a < b) (hb : b < w.length)
    (hpre : ∀ i < a, x + position (wordPath w) i ∉ K)
    (hout : x + position (wordPath w) b ∉ C) :
    wordChildRecords K' C' x F w =
      wordChildRecords K' C' (x + position (wordPath w) a) F (slicePathWord w a b) ++
      wordChildRecords K' C' (x + position (wordPath w) (b + 1)) F
        (slicePathWord w (b + 1) w.length) := by
  change (wordChildIntervals K' C' x w).map _ = _
  unfold wordChildIntervals
  rw [scanChildIntervals_nested_range K C K' C' hKC' hK hC x (wordPath w)
    a b w.length hab hb.le hpre hout, List.map_append]
  rw [wordChildRecords_slice_scan K' C' hKC' x w a b F,
    wordChildRecords_slice_scan K' C' hKC' x w (b + 1) w.length F,
    child_time_block a b hab]
  have hn : w.length - (b + 1) + 1 = w.length - b := by omega
  rw [hn, ← List.range'_eq_map_range]

end SRWTightness
