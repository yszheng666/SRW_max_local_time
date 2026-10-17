import SRWTightness.KilledPathWord

open MeasureTheory

namespace SRWTightness

/-- Scan in chronological order, alternating inner entrance and child-domain exit. -/
def scanChildIntervals (K C : Finset Site) (x : Site) (ω : Sample) :
    Option ℕ → List ℕ → List (ℕ × ℕ)
  | _, [] => []
  | none, i :: is =>
      if x + position ω i ∈ K then scanChildIntervals K C x ω (some i) is
      else scanChildIntervals K C x ω none is
  | some a, i :: is =>
      if x + position ω i ∉ C then (a, i) :: scanChildIntervals K C x ω none is
      else scanChildIntervals K C x ω (some a) is

/-- Complete child intervals in a finite parent word; the parent endpoint is inspected for exit. -/
def wordChildIntervals (K C : Finset Site) (x : Site) (w : PathWord) : List (ℕ × ℕ) :=
  scanChildIntervals K C x (wordPath w) none (List.range (w.length + 1))

/-- Actual complete child intervals before parent exit, using the recorded finite path. -/
noncomputable def killedChildIntervals (D K C : Finset Site) (x : Site) (ω : Sample) :
    List (ℕ × ℕ) := wordChildIntervals K C x (killedPathWord D x ω)

theorem measurableSet_killedChildIntervals_eq (D K C : Finset Site) (x : Site)
    (rs : List (ℕ × ℕ)) : MeasurableSet {ω | killedChildIntervals D K C x ω = rs} := by
  exact (measurable_killedPathWord D x) (Set.to_countable
    {w : PathWord | wordChildIntervals K C x w = rs}).measurableSet

/-- The finite scan emits at most one interval per inspected time. -/
theorem scanChildIntervals_length_le (K C : Finset Site) (x : Site) (ω : Sample)
    (ts : List ℕ) (s : Option ℕ) : (scanChildIntervals K C x ω s ts).length ≤ ts.length := by
  induction ts generalizing s with
  | nil => simp [scanChildIntervals]
  | cons i ts ih =>
    cases s with
    | none =>
      simp only [scanChildIntervals, List.length_cons]
      split_ifs <;> exact le_trans (ih _) (Nat.le_succ _)
    | some a =>
      by_cases hi : x + position ω i ∈ C
      · simpa [scanChildIntervals, hi] using le_trans (ih (some a)) (Nat.le_succ _)
      · simpa [scanChildIntervals, hi] using Nat.succ_le_succ (ih none)

end SRWTightness
