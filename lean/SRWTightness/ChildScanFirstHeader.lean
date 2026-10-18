import SRWTightness.ChildIntervalSeparation

namespace SRWTightness

/-- The first completed interval of a pending scan retains its already recorded entrance. -/
theorem scanChildIntervals_pending_first (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (a : ℕ) (q : ℕ × ℕ) (qs : List (ℕ × ℕ))
    (he : scanChildIntervals K C x ω (some a) ts = q :: qs) : q.1 = a := by
  induction ts with
  | nil => simp [scanChildIntervals] at he
  | cons i ts ih =>
    by_cases hi : x + position ω i ∈ C
    · apply ih
      simpa [scanChildIntervals, hi] using he
    · simpa [scanChildIntervals, hi, eq_comm] using congrArg (fun rs ↦ rs.head?.map Prod.fst) he

/-- Before the first completed child entrance, no inspected earlier site is in the inner target. -/
theorem scanChildIntervals_first_no_visit (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (ht : ts.Pairwise (· < ·)) (q : ℕ × ℕ) (qs : List (ℕ × ℕ))
    (he : scanChildIntervals K C x ω none ts = q :: qs) :
    ∀ i ∈ ts, i < q.1 → x + position ω i ∉ K := by
  induction ts with
  | nil => simp [scanChildIntervals] at he
  | cons j ts ih =>
    obtain ⟨hj, htail⟩ := List.pairwise_cons.mp ht
    by_cases hin : x + position ω j ∈ K
    · have he' : scanChildIntervals K C x ω (some j) ts = q :: qs := by
        simpa [scanChildIntervals, hin] using he
      have hq := scanChildIntervals_pending_first K C x ω ts j q qs he'
      intro i hi hlt
      rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · have hh := hj i hi
        omega
    · have he' : scanChildIntervals K C x ω none ts = q :: qs := by
        simpa [scanChildIntervals, hin] using he
      intro i hi hlt
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hin
      · exact ih htail he' i hi hlt

end SRWTightness
