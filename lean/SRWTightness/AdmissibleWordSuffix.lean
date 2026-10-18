import SRWTightness.AdmissibleWordKilledIdentity
import SRWTightness.PathWordSlice

namespace SRWTightness

/-- Every suffix through the actual exit remains an admissible exit word from its current site. -/
theorem admissibleExitWord_suffix (D : Finset Site) (x e : Site) (w : PathWord)
    (hw : AdmissibleExitWord D x e w) (b : ℕ) (hb : b ≤ w.length) :
    AdmissibleExitWord D (x + position (wordPath w) b) e
      (slicePathWord w b w.length) := by
  refine ⟨?_, ?_, hw.2.2⟩
  · intro i hi
    change i < w.length - b at hi
    rw [slicePathWord_position w b w.length i hi.le, add_assoc, ← position_add]
    exact hw.1 (b + i) (by omega)
  · change (x + position (wordPath w) b) +
      position (wordPath (slicePathWord w b w.length)) (w.length - b) = e
    rw [slicePathWord_position w b w.length (w.length - b) le_rfl,
      add_assoc, ← position_add]
    have he : b + (w.length - b) = w.length := by omega
    rw [he]
    exact hw.2.1

end SRWTightness
