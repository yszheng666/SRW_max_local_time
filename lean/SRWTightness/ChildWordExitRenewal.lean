import SRWTightness.ChildWordFiniteRenewal

namespace SRWTightness

/-- Complete child records renew at the retained exit, including a zero-length terminal suffix. -/
theorem wordChildRecords_exit_renewal {M : Type*} (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (F : Site → PathWord → M) (a b : ℕ)
    (hab : a < b) (hb : b ≤ w.length)
    (hpre : ∀ i < a, x + position (wordPath w) i ∉ K)
    (ha : x + position (wordPath w) a ∈ K)
    (hin : ∀ i, a < i → i < b → x + position (wordPath w) i ∈ C)
    (hout : x + position (wordPath w) b ∉ C) :
    wordChildRecords K C x F w =
      F (x + position (wordPath w) a) (slicePathWord w a b) ::
        wordChildRecords K C (x + position (wordPath w) b) F (slicePathWord w b w.length) := by
  have hnotK : x + position (wordPath w) b ∉ K := fun h ↦ hout (hKC h)
  rw [wordChildRecords_slice_scan K C hKC x w b w.length F]
  change (scanChildIntervals K C x (wordPath w) none (List.range (w.length + 1))).map _ = _
  rw [scanChildIntervals_range_restart K C x (wordPath w) a b w.length hab hb
    hpre ha hin hout, List.map_cons, List.map_map]
  congr 1
  rw [← List.range'_eq_map_range, List.range'_succ]
  simp only [scanChildIntervals, if_neg hnotK]
  have hh := scanChildIntervals_shift K C x (wordPath w) (b + 1)
    (List.range (w.length - b)) none
  simpa only [Option.map_none, List.map_map, List.range'_eq_map_range] using congrArg
    (List.map (fun q ↦ F (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2))) hh.symm

end SRWTightness
