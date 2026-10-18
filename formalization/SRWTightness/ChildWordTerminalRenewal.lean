import SRWTightness.ChildRangeRenewal
import SRWTightness.ActualChildRecords

namespace SRWTightness

/-- When the first child closes at the word endpoint, it is the entire record list. -/
theorem wordChildRecords_terminal_child {M : Type*} (K C : Finset Site)
    (x : Site) (w : PathWord) (F : Site → PathWord → M) (a : ℕ)
    (haN : a < w.length)
    (hpre : ∀ i < a, x + position (wordPath w) i ∉ K)
    (ha : x + position (wordPath w) a ∈ K)
    (hin : ∀ i, a < i → i < w.length → x + position (wordPath w) i ∈ C)
    (hout : x + position (wordPath w) w.length ∉ C) :
    wordChildRecords K C x F w =
      [F (x + position (wordPath w) a) (slicePathWord w a w.length)] := by
  unfold wordChildRecords wordChildIntervals
  rw [scanChildIntervals_range_restart K C x (wordPath w) a w.length w.length
    haN le_rfl hpre ha hin hout]
  simp only [Nat.sub_self, List.range_zero, scanChildIntervals, List.map_nil,
    List.map_cons]

end SRWTightness
