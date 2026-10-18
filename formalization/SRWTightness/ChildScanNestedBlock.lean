import SRWTightness.ChildScanBoundaryReset

namespace SRWTightness

/-- A parent block isolates the nested scan, and the scan resumes empty after that block. -/
theorem scanChildIntervals_nested_block (K C K' C' : Finset Site)
    (hKC' : K' ⊆ C') (hK : K' ⊆ K) (hC : C' ⊆ C)
    (x : Site) (ω : Sample) (pre block tail : List ℕ) (b : ℕ)
    (hpre : ∀ i ∈ pre, x + position ω i ∉ K)
    (hout : x + position ω b ∉ C) :
    scanChildIntervals K' C' x ω none (pre ++ ((block ++ [b]) ++ tail)) =
      scanChildIntervals K' C' x ω none (block ++ [b]) ++
        scanChildIntervals K' C' x ω none tail := by
  rw [scanChildIntervals_skip_prefix K' C' x ω pre]
  · exact scanChildIntervals_append_outside K' C' hKC' x ω block tail b
      (fun h ↦ hout (hC h)) none
  · intro i hi hmem
    exact hpre i hi (hK hmem)

end SRWTightness
