import SRWTightness.ChildSliceScan
import SRWTightness.ChildRangeRenewal

namespace SRWTightness

/-- The interval list renews at its retained first exit, with exactly translated suffix indices. -/
theorem wordChildIntervals_exit_renewal (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (a b : ℕ) (hab : a < b) (hb : b ≤ w.length)
    (hpre : ∀ i < a, x + position (wordPath w) i ∉ K)
    (ha : x + position (wordPath w) a ∈ K)
    (hin : ∀ i, a < i → i < b → x + position (wordPath w) i ∈ C)
    (hout : x + position (wordPath w) b ∉ C) :
    wordChildIntervals K C x w = (a, b) ::
      (wordChildIntervals K C (x + position (wordPath w) b) (slicePathWord w b w.length)).map
        (fun q ↦ (b + q.1, b + q.2)) := by
  have hnotK : x + position (wordPath w) b ∉ K := fun h ↦ hout (hKC h)
  rw [wordChildIntervals_slice_scan K C x w b w.length,
    ← List.range'_eq_map_range, List.range'_succ]
  simp only [scanChildIntervals, if_neg hnotK]
  unfold wordChildIntervals
  rw [scanChildIntervals_range_restart K C x (wordPath w) a b w.length hab hb
    hpre ha hin hout]
  congr 1
  have hh := scanChildIntervals_shift K C x (wordPath w) (b + 1)
    (List.range (w.length - b)) none
  simpa only [Option.map_none, List.range'_eq_map_range] using hh.symm

end SRWTightness
