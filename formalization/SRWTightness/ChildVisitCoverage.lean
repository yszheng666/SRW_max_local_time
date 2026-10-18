import SRWTightness.ChildCompletionWitness

namespace SRWTightness

/-- Every inner-set visit followed by an available exit belongs to a complete extracted child. -/
theorem scanChildIntervals_cover_visit (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (ts : List ℕ) (ht : ts.Pairwise (· < ·)) (s : Option ℕ)
    (j : ℕ) (hj : j ∈ ts) (hvisit : x + position ω j ∈ K)
    (hs : ∀ a, s = some a → a ≤ j)
    (hexit : ∃ k ∈ ts, j < k ∧ x + position ω k ∉ C) :
    ∃ q ∈ scanChildIntervals K C x ω s ts, q.1 ≤ j ∧ j < q.2 := by
  induction ts generalizing s with
  | nil => simp at hj
  | cons i ts ih =>
    obtain ⟨hi, hts⟩ := List.pairwise_cons.mp ht
    have hij : i ≤ j := by
      rcases List.mem_cons.mp hj with he | hj
      · omega
      · exact (hi j hj).le
    have hext : ∃ k ∈ ts, x + position ω k ∉ C := by
      obtain ⟨k, hk, hlt, hout⟩ := hexit
      rcases List.mem_cons.mp hk with he | hk
      · omega
      · exact ⟨k, hk, hout⟩
    have hext' : ∃ k ∈ ts, j < k ∧ x + position ω k ∉ C := by
      obtain ⟨k, hk, hlt, hout⟩ := hexit
      rcases List.mem_cons.mp hk with he | hk
      · omega
      · exact ⟨k, hk, hlt, hout⟩
    by_cases hji : j = i
    · subst j
      cases s with
      | none =>
        simpa [scanChildIntervals, hvisit] using
          scanChildIntervals_pending_covers K C x ω ts i i le_rfl hi hext
      | some a =>
        simpa [scanChildIntervals, hKC hvisit] using
          scanChildIntervals_pending_covers K C x ω ts a i (hs a rfl) hi hext
    · have hjt : j ∈ ts := (List.mem_cons.mp hj).resolve_left hji
      cases s with
      | none =>
        by_cases hin : x + position ω i ∈ K
        · have hp := ih hts (some i) hjt (by intro a he; cases he; exact hij) hext'
          simpa [scanChildIntervals, hin] using hp
        · simpa [scanChildIntervals, hin] using ih hts none hjt hs hext'
      | some a =>
        by_cases hin : x + position ω i ∈ C
        · simpa [scanChildIntervals, hin] using ih hts (some a) hjt hs hext'
        · obtain ⟨q, hq, hcover⟩ := ih hts none hjt (by intro a he; cases he) hext'
          refine ⟨q, ?_, hcover⟩
          simp [scanChildIntervals, hin, hq]

/-- No inner-set visit before the actual parent exit is lost by finite child extraction. -/
theorem killedChildIntervals_cover_visit (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (j : ℕ)
    (hj : j < domainSteps D x ω) (hvisit : x + position ω j ∈ K) :
    ∃ q ∈ killedChildIntervals D K C x ω, q.1 ≤ j ∧ j < q.2 := by
  apply scanChildIntervals_cover_visit K C hKC x (wordPath (killedPathWord D x ω))
    (List.range ((killedPathWord D x ω).length + 1)) List.pairwise_lt_range none j
  · simp only [List.mem_range, killedPathWord]
    omega
  · rw [killedPathWord_position D x ω j hj.le]
    exact hvisit
  · intro a he
    cases he
  · refine ⟨domainSteps D x ω, ?_, hj, ?_⟩
    · simp [killedPathWord]
    · exact killedPathWord_endpoint_outside_child D C hCD x ω hfin

end SRWTightness
