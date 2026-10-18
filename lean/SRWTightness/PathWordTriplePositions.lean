import SRWTightness.PathWordAppendPositions

namespace SRWTightness

/-- Every position in the middle piece is translated by the endpoint of the retained prefix. -/
theorem pathWordAppend_position_middle (p u v : PathWord) (i : ℕ) (hi : i ≤ u.length) :
    position (wordPath (pathWordAppend p (pathWordAppend u v))) (p.length + i) =
      position (wordPath p) p.length + position (wordPath u) i := by
  rw [pathWordAppend_position_right p (pathWordAppend u v) i
    (by rw [pathWordAppend_length]; omega), pathWordAppend_position_left u v i hi]

end SRWTightness
