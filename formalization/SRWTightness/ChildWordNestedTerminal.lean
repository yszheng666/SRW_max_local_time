import SRWTightness.ChildWordNestedRenewal

namespace SRWTightness

/-- A parent block ending at the original endpoint contains every actual nested child record. -/
theorem wordChildRecords_nested_terminal {M : Type*} (K C K' C' : Finset Site)
    (hKC' : K' ⊆ C') (hK : K' ⊆ K) (hC : C' ⊆ C)
    (x : Site) (w : PathWord) (F : Site → PathWord → M) (a : ℕ)
    (haN : a < w.length)
    (hpre : ∀ i < a, x + position (wordPath w) i ∉ K)
    (hout : x + position (wordPath w) w.length ∉ C) :
    wordChildRecords K' C' x F w =
      wordChildRecords K' C' (x + position (wordPath w) a) F
        (slicePathWord w a w.length) := by
  change (wordChildIntervals K' C' x w).map _ = _
  unfold wordChildIntervals
  rw [scanChildIntervals_nested_range K C K' C' hKC' hK hC x (wordPath w)
    a w.length w.length haN le_rfl hpre hout]
  simp only [Nat.sub_self, List.range'_zero, scanChildIntervals, List.append_nil]
  rw [wordChildRecords_slice_scan K' C' hKC' x w a w.length F,
    child_time_block a w.length haN]
  rfl

end SRWTightness
