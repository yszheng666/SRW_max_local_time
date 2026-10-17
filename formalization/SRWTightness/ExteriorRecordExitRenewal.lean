import SRWTightness.ExteriorRecordSliceShift
import SRWTightness.ChildIntervalExitRenewal
import SRWTightness.ChildIntervalSeparation

namespace SRWTightness

/-- Removing the first complete child leaves the exact exterior record of the retained suffix. -/
theorem wordExteriorRecord_exit_renewal (K C : Finset Site) (hKC : K ⊆ C)
    (label : Site → Bool) (x : Site) (w : PathWord) (a b : ℕ)
    (hab : a < b) (hb : b ≤ w.length)
    (hpre : ∀ i < a, x + position (wordPath w) i ∉ K)
    (ha : x + position (wordPath w) a ∈ K)
    (hin : ∀ i, a < i → i < b → x + position (wordPath w) i ∈ C)
    (hout : x + position (wordPath w) b ∉ C) :
    wordExteriorRecord K C label x w =
      let rest := wordExteriorRecord K C label (x + position (wordPath w) b)
        (slicePathWord w b w.length)
      ((slicePathWord w 0 a, label (x + position (wordPath w) a),
        x + position (wordPath w) a, x + position (wordPath w) b) :: rest.1, rest.2) := by
  let v := slicePathWord w b w.length
  let y := x + position (wordPath w) b
  have hs := packExteriorRecord_suffix_shift label x w b 0 hb (Nat.zero_le _)
    (wordChildIntervals K C y v)
    (scanChildIntervals_separated K C y (wordPath v) _ List.pairwise_lt_range none)
    (by
      intro q hq
      have ht := wordChildIntervals_endpoint_le K C y v q hq
      have ho := scanChildIntervals_start_lt_end K C y (wordPath v) _
        List.pairwise_lt_range none (by intro j he; cases he) q hq
      exact ⟨Nat.zero_le _, ho.le, ht.2⟩)
  simp only [Nat.add_zero] at hs
  rw [wordExteriorRecord, wordChildIntervals_exit_renewal K C hKC x w a b hab hb
    hpre ha hin hout]
  simp only [packExteriorRecord]
  rw [← hs]
  rfl

end SRWTightness
