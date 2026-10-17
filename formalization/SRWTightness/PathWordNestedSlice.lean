import SRWTightness.PathWordSlice

namespace SRWTightness

/-- Slicing a child word again preserves the original directions at the translated times. -/
theorem slicePathWord_nested (w : PathWord) (a b c d : ℕ)
    (hcd : c ≤ d) (hd : d ≤ b - a) :
    slicePathWord (slicePathWord w a b) c d = slicePathWord w (a + c) (a + d) := by
  simp only [slicePathWord]
  congr 1
  · omega
  · apply (Fin.heq_fun_iff (show d - c = a + d - (a + c) by omega)).mpr
    intro k
    have hk : c + k.val < b - a := by omega
    simp [wordPath, extendWord, hk, Nat.add_assoc]

end SRWTightness
