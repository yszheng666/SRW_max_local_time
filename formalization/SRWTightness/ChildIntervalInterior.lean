import SRWTightness.ChildIntervalEndpoints

namespace SRWTightness

/-- A consecutive scan keeps every emitted interval inside the child domain before its exit. -/
theorem scanChildIntervals_interior (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (n start : ℕ) (s : Option ℕ)
    (hs : ∀ a, s = some a → ∀ k, a ≤ k → k < start → x + position ω k ∈ C)
    (q : ℕ × ℕ) (hq : q ∈ scanChildIntervals K C x ω s (List.range' start n)) :
    ∀ k, q.1 ≤ k → k < q.2 → x + position ω k ∈ C := by
  induction n generalizing start s with
  | zero => simp [scanChildIntervals] at hq
  | succ n ih =>
    rw [List.range'_succ] at hq
    cases s with
    | none =>
      by_cases hi : x + position ω start ∈ K
      · simp only [scanChildIntervals, if_pos hi] at hq
        apply ih (start + 1) (some start) _ hq
        intro a he k hak hk
        cases he
        have heq : k = start := by omega
        subst k
        exact hKC hi
      · simp only [scanChildIntervals, if_neg hi] at hq
        exact ih (start + 1) none (by intro a he; cases he) hq
    | some a =>
      by_cases hi : x + position ω start ∉ C
      · simp only [scanChildIntervals, if_pos hi, List.mem_cons] at hq
        rcases hq with he | hq
        · subst q
          exact hs a rfl
        · exact ih (start + 1) none (by intro a he; cases he) hq
      · simp only [scanChildIntervals, if_neg hi] at hq
        apply ih (start + 1) (some a) _ hq
        intro a' he k hak hk
        cases he
        by_cases hlt : k < start
        · exact hs a rfl k hak hlt
        · have heq : k = start := by omega
          subst k
          exact not_not.mp hi

/-- Every finite extracted child stays in its domain throughout its half-open interval. -/
theorem wordChildIntervals_interior (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (q : ℕ × ℕ) (hq : q ∈ wordChildIntervals K C x w) :
    ∀ k, q.1 ≤ k → k < q.2 → x + position (wordPath w) k ∈ C := by
  apply scanChildIntervals_interior K C hKC x (wordPath w) (w.length + 1) 0 none
    (by intro a he; cases he) q
  simpa only [wordChildIntervals, List.range_eq_range'] using hq

end SRWTightness
