import SRWTightness.ChildActualRenewal
import SRWTightness.PathWordNestedSlice

namespace SRWTightness

/-- A scan of a sliced word is the original scan on its translated observation interval. -/
theorem wordChildIntervals_slice_scan (K C : Finset Site) (x : Site) (w : PathWord)
    (a b : ℕ) :
    (wordChildIntervals K C (x + position (wordPath w) a)
      (slicePathWord w a b)).map (fun q ↦ (a + q.1, a + q.2)) =
      scanChildIntervals K C x (wordPath w) none
        ((List.range (b - a + 1)).map (a + ·)) := by
  unfold wordChildIntervals
  change (scanChildIntervals K C (x + position (wordPath w) a)
    (wordPath (slicePathWord w a b)) none (List.range (b - a + 1))).map _ = _
  rw [scanChildIntervals_position_congr K C _ _ (shift a (wordPath w))]
  · exact (scanChildIntervals_shift K C x (wordPath w) a
      (List.range (b - a + 1)) none).symm
  · intro i hi
    apply slicePathWord_position
    simp only [List.mem_range] at hi
    omega

end SRWTightness
