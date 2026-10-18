import SRWTightness.FirstEntranceWordPrefix

namespace SRWTightness

/-- Extract the first-entry ordered mark from a finite parent path. -/
noncomputable def firstEntranceWordOfWord (D K : Finset Site) (x : Site)
    (w : PathWord) : WordMark := firstEntranceWordMark D K x (wordPath w)

/-- The finite parent word retains its actual first-entry ordered mark. -/
theorem firstEntranceWordOfWord_killedPathWord (D K : Finset Site) (x : Site)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    firstEntranceWordOfWord D K x (killedPathWord D x ω) =
      firstEntranceWordMark D K x ω := by
  symm
  apply firstEntranceWordMark_eq_of_prefix D K x ω _ hfin
  intro i hi
  simp [wordPath, killedPathWord, extendWord, hi]

/-- The finite-word extraction agrees almost surely with the original path extraction. -/
theorem firstEntranceWordOfWord_killedPathWord_ae (D K : Finset Site) (x : Site) :
    (fun ω ↦ firstEntranceWordOfWord D K x (killedPathWord D x ω)) =ᵐ[pathLaw]
      firstEntranceWordMark D K x := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  exact firstEntranceWordOfWord_killedPathWord D K x ω hω

end SRWTightness
