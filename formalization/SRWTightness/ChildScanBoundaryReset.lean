import SRWTightness.ChildScanRenewal

namespace SRWTightness

/-- Inspecting an outside endpoint resets the scanner before any later observation segment. -/
theorem scanChildIntervals_append_outside (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (pre tail : List ℕ) (b : ℕ)
    (hout : x + position ω b ∉ C) (s : Option ℕ) :
    scanChildIntervals K C x ω s ((pre ++ [b]) ++ tail) =
      scanChildIntervals K C x ω s (pre ++ [b]) ++
        scanChildIntervals K C x ω none tail := by
  induction pre generalizing s with
  | nil =>
    have hnotK : x + position ω b ∉ K := fun h ↦ hout (hKC h)
    cases s <;> simp [scanChildIntervals, hout, hnotK]
  | cons i pre ih =>
    cases s with
    | none =>
      by_cases hi : x + position ω i ∈ K
      · simpa [scanChildIntervals, hi] using ih (some i)
      · simpa [scanChildIntervals, hi] using ih none
    | some a =>
      by_cases hi : x + position ω i ∈ C
      · simpa [scanChildIntervals, hi] using ih (some a)
      · simpa [scanChildIntervals, hi] using congrArg (List.cons (a, i)) (ih none)

end SRWTightness
