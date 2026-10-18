import SRWTightness.PathWordDirections

namespace SRWTightness

/-- An actual slice has exactly the corresponding finite direction sublist. -/
theorem pathWordDirections_slice (w : PathWord) (a b : ℕ) (hb : b ≤ w.length) :
    pathWordDirections (slicePathWord w a b) =
      ((pathWordDirections w).drop a).take (b - a) := by
  apply List.ext_getElem
  · simp only [pathWordDirections, List.length_ofFn, slicePathWord, List.length_take,
      List.length_drop]
    omega
  · intro i hi hj
    have hi' : i < b - a := by simpa [pathWordDirections, slicePathWord] using hi
    have hw : a + i < w.length := by omega
    simp [pathWordDirections, slicePathWord, wordPath, extendWord, hw]

/-- Consecutive slices concatenate to the full slice, with no duplicated direction. -/
theorem pathWordAppend_slices (w : PathWord) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ w.length) :
    pathWordAppend (slicePathWord w a b) (slicePathWord w b c) = slicePathWord w a c := by
  apply pathWordDirections_injective
  rw [pathWordDirections_append, pathWordDirections_slice w a b (hbc.trans hc),
    pathWordDirections_slice w b c hc, pathWordDirections_slice w a c hc]
  have he : c - a = (b - a) + (c - b) := by omega
  have hb' : a + (b - a) = b := by omega
  rw [he, List.take_add, List.drop_drop, hb']

/-- Slicing a word from its initial time to its full length preserves the word. -/
theorem slicePathWord_full (w : PathWord) : slicePathWord w 0 w.length = w := by
  apply pathWordDirections_injective
  rw [pathWordDirections_slice w 0 w.length le_rfl]
  simp [pathWordDirections]

end SRWTightness
