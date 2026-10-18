import SRWTightness.ChildSliceScan
import SRWTightness.ActualChildRecords

namespace SRWTightness

/-- Translated slice intervals produce exactly the same sites and direction words. -/
theorem wordChildRecords_slice_scan {M : Type*} (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (a b : ℕ) (F : Site → PathWord → M) :
    wordChildRecords K C (x + position (wordPath w) a) F (slicePathWord w a b) =
      (scanChildIntervals K C x (wordPath w) none
        ((List.range (b - a + 1)).map (a + ·))).map
        (fun q ↦ F (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2)) := by
  rw [← wordChildIntervals_slice_scan K C x w a b, List.map_map]
  unfold wordChildRecords
  apply List.map_congr_left
  intro q hq
  have ht := wordChildIntervals_endpoint_le K C
    (x + position (wordPath w) a) (slicePathWord w a b) q hq
  have hlt := scanChildIntervals_start_lt_end K C
    (x + position (wordPath w) a) (wordPath (slicePathWord w a b)) _
    List.pairwise_lt_range none (by intro j h; cases h) q hq
  change F ((x + position (wordPath w) a) +
    position (wordPath (slicePathWord w a b)) q.1)
    (slicePathWord (slicePathWord w a b) q.1 q.2) = _
  rw [slicePathWord_nested w a b q.1 q.2 hlt.le ht.2,
    slicePathWord_position w a b q.1 ht.1]
  rw [add_assoc, ← position_add]
  rfl

end SRWTightness
