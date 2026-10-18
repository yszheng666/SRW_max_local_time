import SRWTightness.ChildIntervalExtraction

namespace SRWTightness

/-- Every emitted pair starts in the inner set and ends outside the child domain. -/
theorem scanChildIntervals_endpoints (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (s : Option ℕ)
    (hs : ∀ a, s = some a → x + position ω a ∈ K) (q : ℕ × ℕ)
    (hq : q ∈ scanChildIntervals K C x ω s ts) :
    x + position ω q.1 ∈ K ∧ x + position ω q.2 ∉ C := by
  induction ts generalizing s with
  | nil => simp [scanChildIntervals] at hq
  | cons i ts ih =>
    cases s with
    | none =>
      by_cases hi : x + position ω i ∈ K
      · simp only [scanChildIntervals, if_pos hi] at hq
        apply ih (some i) _ hq
        intro a he
        cases he
        exact hi
      · simp only [scanChildIntervals, if_neg hi] at hq
        exact ih none hs hq
    | some a =>
      by_cases hi : x + position ω i ∉ C
      · simp [scanChildIntervals, hi] at hq
        rcases hq with he | hq
        · subst q
          exact ⟨hs a rfl, hi⟩
        · exact ih none (by intro z hz; cases hz) hq
      · simp [scanChildIntervals, hi] at hq
        exact ih (some a) hs hq

/-- The concrete finite-word extractor retains the required entrance and exit endpoints. -/
theorem wordChildIntervals_endpoints (K C : Finset Site) (x : Site) (w : PathWord)
    (q : ℕ × ℕ) (hq : q ∈ wordChildIntervals K C x w) :
    x + position (wordPath w) q.1 ∈ K ∧ x + position (wordPath w) q.2 ∉ C :=
  scanChildIntervals_endpoints K C x (wordPath w) _ none (by intro a h; cases h) q hq

end SRWTightness
