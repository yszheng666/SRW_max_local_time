import SRWTightness.PathWordDirections

namespace SRWTightness

/-- Before the junction, concatenation has exactly the first word's increments. -/
theorem pathWordAppend_direction_left (u v : PathWord) (i : ℕ) (hi : i < u.length) :
    wordPath (pathWordAppend u v) i = wordPath u i := by
  have ht : i < u.length + v.length := by omega
  simp [wordPath, pathWordAppend, pathWordOfDirections, pathWordDirections,
    extendWord, hi, ht, List.getElem_append_left]

/-- After the junction, concatenation has exactly the second word's recorded increments. -/
theorem pathWordAppend_direction_right (u v : PathWord) (i : ℕ) (hi : i < v.length) :
    wordPath (pathWordAppend u v) (u.length + i) = wordPath v i := by
  have ht : u.length + i < u.length + v.length := by omega
  have hn : ¬u.length + i < u.length := by omega
  simp [wordPath, pathWordAppend, pathWordOfDirections, pathWordDirections,
    extendWord, hi, ht, hn, List.getElem_append_right]

/-- Positions through the junction agree with the first word. -/
theorem pathWordAppend_position_left (u v : PathWord) (i : ℕ) (hi : i ≤ u.length) :
    position (wordPath (pathWordAppend u v)) i = position (wordPath u) i := by
  apply position_congr
  intro k hk
  exact pathWordAppend_direction_left u v k (hk.trans_le hi)

/-- Positions after the junction are translated positions of the second word. -/
theorem pathWordAppend_position_right (u v : PathWord) (i : ℕ) (hi : i ≤ v.length) :
    position (wordPath (pathWordAppend u v)) (u.length + i) =
      position (wordPath u) u.length + position (wordPath v) i := by
  rw [position_add, pathWordAppend_position_left u v u.length le_rfl]
  congr 1
  apply position_congr
  intro k hk
  exact pathWordAppend_direction_right u v k (hk.trans_le hi)

end SRWTightness
