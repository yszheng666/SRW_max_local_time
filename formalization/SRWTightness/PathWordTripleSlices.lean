import SRWTightness.PathWordAppendSlices
import SRWTightness.PathWordNestedSlice

namespace SRWTightness

/-- The middle word is recovered exactly from a three-piece concatenation. -/
theorem pathWordAppend_slice_middle (p u v : PathWord) :
    slicePathWord (pathWordAppend p (pathWordAppend u v)) p.length (p.length + u.length) = u := by
  let w := pathWordAppend p (pathWordAppend u v)
  have hh := slicePathWord_nested w p.length w.length 0 u.length (Nat.zero_le _)
    (by dsimp [w]; rw [pathWordAppend_length, pathWordAppend_length]; omega)
  have hs : slicePathWord w p.length w.length = pathWordAppend u v := by
    dsimp [w]
    rw [pathWordAppend_length]
    exact pathWordAppend_slice_right p (pathWordAppend u v)
  rw [hs, pathWordAppend_slice_left, Nat.add_zero] at hh
  exact hh.symm

/-- The final word is recovered exactly from a three-piece concatenation. -/
theorem pathWordAppend_slice_final (p u v : PathWord) :
    slicePathWord (pathWordAppend p (pathWordAppend u v)) (p.length + u.length)
      (pathWordAppend p (pathWordAppend u v)).length = v := by
  let w := pathWordAppend p (pathWordAppend u v)
  have hh := slicePathWord_nested w p.length w.length u.length
    (u.length + v.length) (by omega)
    (by dsimp [w]; rw [pathWordAppend_length, pathWordAppend_length]; omega)
  have hs : slicePathWord w p.length w.length = pathWordAppend u v := by
    dsimp [w]
    rw [pathWordAppend_length]
    exact pathWordAppend_slice_right p (pathWordAppend u v)
  rw [hs, pathWordAppend_slice_right] at hh
  have hl : p.length + (u.length + v.length) = w.length := by
    simp [w, pathWordAppend_length]
  rw [hl] at hh
  exact hh.symm

end SRWTightness
