import SRWTightness.ChildIntervalRange

namespace SRWTightness

/-- An increasing scan cannot emit an empty or reversed child interval. -/
theorem scanChildIntervals_start_lt_end (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (ht : ts.Pairwise (· < ·)) (s : Option ℕ)
    (hs : ∀ a, s = some a → ∀ i ∈ ts, a < i) (q : ℕ × ℕ)
    (hq : q ∈ scanChildIntervals K C x ω s ts) : q.1 < q.2 := by
  induction ts generalizing s with
  | nil => simp [scanChildIntervals] at hq
  | cons i ts ih =>
    obtain ⟨hi, hts⟩ := List.pairwise_cons.mp ht
    cases s with
    | none =>
      by_cases hin : x + position ω i ∈ K
      · simp [scanChildIntervals, hin] at hq
        apply ih hts (some i) _ hq
        intro a he j hj
        cases he
        exact hi j hj
      · simp [scanChildIntervals, hin] at hq
        exact ih hts none (by intro a he; cases he) hq
    | some a =>
      by_cases hin : x + position ω i ∈ C
      · simp [scanChildIntervals, hin] at hq
        exact ih hts (some a) (fun b hb j hj ↦ hs b hb j (List.mem_cons_of_mem i hj)) hq
      · simp [scanChildIntervals, hin] at hq
        rcases hq with he | hq
        · subst q
          exact hs a rfl i List.mem_cons_self
        · exact ih hts none (by intro b he; cases he) hq

theorem killedChildIntervals_start_lt_end (D K C : Finset Site) (x : Site) (ω : Sample)
    (q : ℕ × ℕ) (hq : q ∈ killedChildIntervals D K C x ω) : q.1 < q.2 :=
  scanChildIntervals_start_lt_end K C x (wordPath (killedPathWord D x ω)) _
    List.pairwise_lt_range none (by intro a h; cases h) q hq

end SRWTightness
