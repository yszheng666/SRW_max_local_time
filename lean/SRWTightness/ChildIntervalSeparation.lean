import SRWTightness.ChildIntervalOrder

namespace SRWTightness

/-- Earlier completed children finish strictly before later children begin. -/
theorem scanChildIntervals_separated (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (ht : ts.Pairwise (· < ·)) (s : Option ℕ) :
    (scanChildIntervals K C x ω s ts).Pairwise (fun a b ↦ a.2 < b.1) := by
  induction ts generalizing s with
  | nil => simp [scanChildIntervals]
  | cons i ts ih =>
    obtain ⟨hi, hts⟩ := List.pairwise_cons.mp ht
    cases s with
    | none =>
      by_cases hin : x + position ω i ∈ K
      · simpa [scanChildIntervals, hin] using ih hts (some i)
      · simpa [scanChildIntervals, hin] using ih hts none
    | some a =>
      by_cases hin : x + position ω i ∈ C
      · simpa [scanChildIntervals, hin] using ih hts (some a)
      · simp only [scanChildIntervals, hin, not_false_eq_true, if_true]
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih hts none⟩
        intro q hq
        have he := (scanChildIntervals_endpoint_times K C x ω ts none q hq).1
        rcases he with he | he
        · exact hi q.1 he
        · cases he

theorem killedChildIntervals_separated (D K C : Finset Site) (x : Site) (ω : Sample) :
    (killedChildIntervals D K C x ω).Pairwise (fun a b ↦ a.2 < b.1) :=
  scanChildIntervals_separated K C x (wordPath (killedPathWord D x ω)) _
    List.pairwise_lt_range none

end SRWTightness
