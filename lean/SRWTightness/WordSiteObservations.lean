import SRWTightness.PathWordSlice

namespace SRWTightness

/-- The observed positions of a finite direction word, including both endpoints. -/
def wordSiteObservations (x : Site) (w : PathWord) : List Site :=
  (List.range (w.length + 1)).map (fun i ↦ x + position (wordPath w) i)

/-- Slicing a direction word gives precisely the corresponding inclusive position list. -/
theorem wordSiteObservations_slice (x : Site) (w : PathWord) (a b : ℕ) :
    wordSiteObservations (x + position (wordPath w) a) (slicePathWord w a b) =
      (List.range' a (b - a + 1)).map (fun i ↦ x + position (wordPath w) i) := by
  rw [List.range'_eq_map_range, List.map_map]
  unfold wordSiteObservations
  change (List.range (b - a + 1)).map _ = _
  apply List.map_congr_left
  intro i hi
  have hi' : i ≤ b - a := by simpa using List.mem_range.mp hi
  rw [slicePathWord_position w a b i hi', add_assoc, ← position_add]
  rfl

end SRWTightness
