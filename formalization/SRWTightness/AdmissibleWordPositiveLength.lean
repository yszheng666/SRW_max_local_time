import SRWTightness.AdmissibleWordKilledIdentity

namespace SRWTightness

/-- A genuine exit word starting inside its domain must contain at least one step. -/
theorem admissibleExitWord_length_pos (C : Finset Site) (x e : Site) (w : PathWord)
    (hx : x ∈ C) (hw : AdmissibleExitWord C x e w) : 0 < w.length := by
  by_contra hn
  have hl : w.length = 0 := by omega
  have he : x = e := by simpa [hl, position] using hw.2.1
  exact hw.2.2 (he ▸ hx)

end SRWTightness
