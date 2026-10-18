import SRWTightness.PathWordDirectionsSlice

namespace SRWTightness

/-- The initial slice of a concatenation is exactly its first word. -/
theorem pathWordAppend_slice_left (u v : PathWord) :
    slicePathWord (pathWordAppend u v) 0 u.length = u := by
  apply pathWordDirections_injective
  rw [pathWordDirections_slice _ _ _ (by rw [pathWordAppend_length]; omega),
    pathWordDirections_append]
  have hu : (pathWordDirections u).length = u.length := List.length_ofFn
  simp only [Nat.sub_zero, List.drop_zero]
  rw [← hu, List.take_left]

/-- The final slice of a concatenation is exactly its second word. -/
theorem pathWordAppend_slice_right (u v : PathWord) :
    slicePathWord (pathWordAppend u v) u.length (u.length + v.length) = v := by
  apply pathWordDirections_injective
  rw [pathWordDirections_slice _ _ _ (by rw [pathWordAppend_length]),
    pathWordDirections_append]
  have hu : (pathWordDirections u).length = u.length := List.length_ofFn
  have hv : (pathWordDirections v).length = v.length := List.length_ofFn
  rw [Nat.add_sub_cancel_left, ← hu, List.drop_left, ← hv, List.take_length]

end SRWTightness
