import SRWTightness.ChildIntervalExtraction

namespace SRWTightness

/-- Chronological inward entrances, including a last entrance whose exit is not in the inspected list. -/
def scanChildEntrances (K C : Finset Site) (x : Site) (ω : Sample) :
    Option ℕ → List ℕ → List ℕ
  | _, [] => []
  | none, i :: is =>
      if x + position ω i ∈ K then i :: scanChildEntrances K C x ω (some i) is
      else scanChildEntrances K C x ω none is
  | some a, i :: is =>
      if x + position ω i ∉ C then scanChildEntrances K C x ω none is
      else scanChildEntrances K C x ω (some a) is

/-- Completed intervals cannot outnumber entrances plus the interval already pending at scan start. -/
theorem scanChildIntervals_length_le_entrances (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (s : Option ℕ) :
    (scanChildIntervals K C x ω s ts).length ≤
      (scanChildEntrances K C x ω s ts).length + if s.isSome then 1 else 0 := by
  induction ts generalizing s with
  | nil => cases s <;> simp [scanChildIntervals, scanChildEntrances]
  | cons i ts ih =>
    cases s with
    | none =>
      by_cases hi : x + position ω i ∈ K
      · simpa [scanChildIntervals, scanChildEntrances, hi, Nat.add_comm] using ih (some i)
      · simpa [scanChildIntervals, scanChildEntrances, hi] using ih none
    | some a =>
      by_cases hi : x + position ω i ∈ C
      · simpa [scanChildIntervals, scanChildEntrances, hi] using ih (some a)
      · simpa [scanChildIntervals, scanChildEntrances, hi] using Nat.succ_le_succ (ih none)

/-- A final inspection outside the outer domain completes every pending entrance. -/
theorem scanChildIntervals_length_eq_entrances_at_exit (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (ts : List ℕ) (e : ℕ) (he : x + position ω e ∉ C)
    (s : Option ℕ) :
    (scanChildIntervals K C x ω s (ts ++ [e])).length =
      (scanChildEntrances K C x ω s (ts ++ [e])).length + if s.isSome then 1 else 0 := by
  have heK : x + position ω e ∉ K := fun h ↦ he (hKC h)
  induction ts generalizing s with
  | nil => cases s <;> simp [scanChildIntervals, scanChildEntrances, heK, he]
  | cons i ts ih =>
    cases s with
    | none =>
      by_cases hi : x + position ω i ∈ K
      · simpa [scanChildIntervals, scanChildEntrances, hi, Nat.add_comm] using ih (some i)
      · simpa [scanChildIntervals, scanChildEntrances, hi] using ih none
    | some a =>
      by_cases hi : x + position ω i ∈ C
      · simpa [scanChildIntervals, scanChildEntrances, hi] using ih (some a)
      · simpa [scanChildIntervals, scanChildEntrances, hi] using congrArg Nat.succ (ih none)

/-- All inward entrance times inspected in the finite word, including its terminal position. -/
def wordChildEntranceTimes (K C : Finset Site) (x : Site) (w : PathWord) : List ℕ :=
  scanChildEntrances K C x (wordPath w) none (List.range (w.length + 1))

/-- An outer-exit endpoint makes the complete-interval count equal the full entrance count. -/
theorem wordChildIntervals_length_eq_entrances (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (he : x + position (wordPath w) w.length ∉ C) :
    (wordChildIntervals K C x w).length = (wordChildEntranceTimes K C x w).length := by
  unfold wordChildIntervals wordChildEntranceTimes
  rw [List.range_succ]
  simpa using scanChildIntervals_length_eq_entrances_at_exit K C hKC x (wordPath w)
    (List.range w.length) w.length he none

end SRWTightness
