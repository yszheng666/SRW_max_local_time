import SRWTightness.ChildCompetingEntrance

namespace SRWTightness

/-- A pending child consumes its interior and restarts the same scanner after its exit. -/
theorem scanChildIntervals_close_restart (K C : Finset Site) (x : Site) (ω : Sample)
    (a b : ℕ) (inside tail : List ℕ)
    (hin : ∀ i ∈ inside, x + position ω i ∈ C) (hout : x + position ω b ∉ C) :
    scanChildIntervals K C x ω (some a) (inside ++ b :: tail) =
      (a, b) :: scanChildIntervals K C x ω none tail := by
  induction inside with
  | nil => simp [scanChildIntervals, hout]
  | cons i inside ih =>
    have hi := hin i List.mem_cons_self
    simpa [scanChildIntervals, hi] using
      ih (fun j hj ↦ hin j (List.mem_cons_of_mem i hj))

/-- The exact remainder after the first complete child is the scan of the remaining times. -/
theorem scanChildIntervals_first_child_restart (K C : Finset Site) (x : Site) (ω : Sample)
    (a b : ℕ) (pre inside tail : List ℕ)
    (hpre : ∀ i ∈ pre, x + position ω i ∉ K)
    (ha : x + position ω a ∈ K) (hin : ∀ i ∈ inside, x + position ω i ∈ C)
    (hout : x + position ω b ∉ C) :
    scanChildIntervals K C x ω none (pre ++ a :: (inside ++ b :: tail)) =
      (a, b) :: scanChildIntervals K C x ω none tail := by
  rw [scanChildIntervals_skip_prefix K C x ω pre _ hpre]
  simpa [scanChildIntervals, ha] using
    scanChildIntervals_close_restart K C x ω a b inside tail hin hout

/-- Translating scan times is exactly scanning the shifted walk from its actual current site. -/
theorem scanChildIntervals_shift (K C : Finset Site) (x : Site) (ω : Sample)
    (a : ℕ) (ts : List ℕ) (s : Option ℕ) :
    scanChildIntervals K C x ω (s.map (a + ·)) (ts.map (a + ·)) =
      (scanChildIntervals K C (x + position ω a) (shift a ω) s ts).map
        (fun q ↦ (a + q.1, a + q.2)) := by
  induction ts generalizing s with
  | nil => simp [scanChildIntervals]
  | cons i ts ih =>
    cases s with
    | none =>
      by_cases hi : (x + position ω a) + position (shift a ω) i ∈ K
      · simpa [scanChildIntervals, position_add, ← add_assoc, hi] using ih (some i)
      · simpa [scanChildIntervals, position_add, ← add_assoc, hi] using ih none
    | some j =>
      by_cases hi : (x + position ω a) + position (shift a ω) i ∈ C
      · simpa [scanChildIntervals, position_add, ← add_assoc, hi] using ih (some j)
      · simpa [scanChildIntervals, position_add, ← add_assoc, hi] using
          congrArg (List.cons (a + j, a + i)) (ih none)

end SRWTightness
