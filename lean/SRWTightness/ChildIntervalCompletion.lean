import SRWTightness.ChildIntervalSeparation

namespace SRWTightness

/-- A pending child is completed whenever the remaining scan includes an exit from its domain. -/
theorem scanChildIntervals_pending_completed (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (a : ℕ) (hexit : ∃ i ∈ ts, x + position ω i ∉ C) :
    ∃ q ∈ scanChildIntervals K C x ω (some a) ts, q.1 = a := by
  induction ts with
  | nil => simpa using hexit
  | cons i ts ih =>
    by_cases hi : x + position ω i ∈ C
    · have ht : ∃ j ∈ ts, x + position ω j ∉ C := by
        obtain ⟨j, hj, hout⟩ := hexit
        rcases List.mem_cons.mp hj with he | hj
        · subst j
          exact False.elim (hout hi)
        · exact ⟨j, hj, hout⟩
      simpa [scanChildIntervals, hi] using ih ht
    · refine ⟨(a, i), ?_, rfl⟩
      simp [scanChildIntervals, hi]

/-- Starting a child before a later available exit creates a complete recorded interval. -/
theorem scanChildIntervals_entry_completed (K C : Finset Site) (x : Site) (ω : Sample)
    (i : ℕ) (ts : List ℕ) (hi : x + position ω i ∈ K)
    (hexit : ∃ j ∈ ts, x + position ω j ∉ C) :
    ∃ q ∈ scanChildIntervals K C x ω none (i :: ts), q.1 = i := by
  simpa [scanChildIntervals, hi] using
    scanChildIntervals_pending_completed K C x ω ts i hexit

end SRWTightness
