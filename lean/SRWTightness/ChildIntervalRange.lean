import SRWTightness.ChildIntervalEndpoints

namespace SRWTightness

/-- Emitted endpoints come from inspected times or the already active entrance. -/
theorem scanChildIntervals_endpoint_times (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (s : Option ℕ) (q : ℕ × ℕ)
    (hq : q ∈ scanChildIntervals K C x ω s ts) :
    (q.1 ∈ ts ∨ s = some q.1) ∧ q.2 ∈ ts := by
  induction ts generalizing s with
  | nil => simp [scanChildIntervals] at hq
  | cons i ts ih =>
    cases s with
    | none =>
      by_cases hi : x + position ω i ∈ K
      · simp [scanChildIntervals, hi] at hq
        obtain ⟨hl, hu⟩ := ih (some i) hq
        refine ⟨Or.inl ?_, List.mem_cons_of_mem i hu⟩
        rcases hl with hl | hl
        · exact List.mem_cons_of_mem i hl
        · have he : i = q.1 := Option.some.inj hl
          simp [he]
      · simp [scanChildIntervals, hi] at hq
        obtain ⟨hl, hu⟩ := ih none hq
        exact ⟨hl.imp (List.mem_cons_of_mem i) id, List.mem_cons_of_mem i hu⟩
    | some a =>
      by_cases hi : x + position ω i ∈ C
      · simp [scanChildIntervals, hi] at hq
        obtain ⟨hl, hu⟩ := ih (some a) hq
        exact ⟨hl.imp (List.mem_cons_of_mem i) id, List.mem_cons_of_mem i hu⟩
      · simp [scanChildIntervals, hi] at hq
        rcases hq with he | hq
        · subst q
          exact ⟨Or.inr rfl, List.mem_cons_self⟩
        · obtain ⟨hl, hu⟩ := ih none hq
          rcases hl with hl | hl
          · exact ⟨Or.inl (List.mem_cons_of_mem i hl), List.mem_cons_of_mem i hu⟩
          · cases hl

theorem wordChildIntervals_endpoint_le (K C : Finset Site) (x : Site) (w : PathWord)
    (q : ℕ × ℕ) (hq : q ∈ wordChildIntervals K C x w) :
    q.1 ≤ w.length ∧ q.2 ≤ w.length := by
  obtain ⟨hl, hu⟩ := scanChildIntervals_endpoint_times K C x (wordPath w) _ none q hq
  rcases hl with hl | hl
  · simp only [List.mem_range] at hl hu
    omega
  · cases hl

/-- Extracted child endpoints are genuine positions of the original killed path. -/
theorem killedChildIntervals_endpoints (D K C : Finset Site) (x : Site) (ω : Sample)
    (q : ℕ × ℕ) (hq : q ∈ killedChildIntervals D K C x ω) :
    x + position ω q.1 ∈ K ∧ x + position ω q.2 ∉ C := by
  have ht := wordChildIntervals_endpoint_le K C x (killedPathWord D x ω) q hq
  have he := wordChildIntervals_endpoints K C x (killedPathWord D x ω) q hq
  rw [killedPathWord_position D x ω q.1 ht.1,
    killedPathWord_position D x ω q.2 ht.2] at he
  exact he

end SRWTightness
