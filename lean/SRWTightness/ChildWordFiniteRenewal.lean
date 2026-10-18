import SRWTightness.ChildSliceRecords
import SRWTightness.ChildRangeRenewal

namespace SRWTightness

/-- A finite word record list renews after its first complete child, with exact remaining word. -/
theorem wordChildRecords_finite_renewal {M : Type*} (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (F : Site → PathWord → M) (a b : ℕ)
    (hab : a < b) (hb : b < w.length)
    (hpre : ∀ i < a, x + position (wordPath w) i ∉ K)
    (ha : x + position (wordPath w) a ∈ K)
    (hin : ∀ i, a < i → i < b → x + position (wordPath w) i ∈ C)
    (hout : x + position (wordPath w) b ∉ C) :
    wordChildRecords K C x F w =
      F (x + position (wordPath w) a) (slicePathWord w a b) ::
      wordChildRecords K C (x + position (wordPath w) (b + 1)) F
        (slicePathWord w (b + 1) w.length) := by
  change (wordChildIntervals K C x w).map _ = _
  unfold wordChildIntervals
  rw [scanChildIntervals_range_restart K C x (wordPath w) a b w.length hab hb.le
    hpre ha hin hout, List.map_cons, List.map_map]
  congr 1
  rw [wordChildRecords_slice_scan K C hKC x w (b + 1) w.length F]
  have hn : w.length - (b + 1) + 1 = w.length - b := by omega
  rw [hn]
  have hh := scanChildIntervals_shift K C x (wordPath w) (b + 1)
    (List.range (w.length - b)) none
  simpa only [Option.map_none, List.map_map] using congrArg
    (List.map (fun q ↦ F (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2)))
    hh.symm

end SRWTightness
