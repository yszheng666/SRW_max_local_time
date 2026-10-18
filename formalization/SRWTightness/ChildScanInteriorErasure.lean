import SRWTightness.ChildScanRenewal

namespace SRWTightness

/-- A pending excursion ignores any list of observations inside its domain. -/
theorem scanChildIntervals_erase_inside (K C : Finset Site) (x : Site) (ω : Sample)
    (a : ℕ) (inside tail : List ℕ)
    (hin : ∀ i ∈ inside, x + position ω i ∈ C) :
    scanChildIntervals K C x ω (some a) (inside ++ tail) =
      scanChildIntervals K C x ω (some a) tail := by
  induction inside with
  | nil => rfl
  | cons i inside ih =>
    have hi := hin i List.mem_cons_self
    simpa only [List.cons_append, scanChildIntervals, not_not.mpr hi, if_false] using
      ih (fun j hj ↦ hin j (List.mem_cons_of_mem i hj))

/-- After a retained inner observation, deleting further interior observations is invisible. -/
theorem scanChildIntervals_erase_after_entrance (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (a : ℕ) (inside tail : List ℕ) (s : Option ℕ)
    (ha : x + position ω a ∈ K)
    (hin : ∀ i ∈ inside, x + position ω i ∈ C) :
    scanChildIntervals K C x ω s (a :: (inside ++ tail)) =
      scanChildIntervals K C x ω s (a :: tail) := by
  cases s with
  | none =>
    simpa only [scanChildIntervals, if_pos ha] using
      scanChildIntervals_erase_inside K C x ω a inside tail hin
  | some b =>
    have haC := hKC ha
    simpa only [scanChildIntervals, not_not.mpr haC, if_false] using
      scanChildIntervals_erase_inside K C x ω b inside tail hin

/-- Interior erasure remains valid after an arbitrary preceding observation list. -/
theorem scanChildIntervals_erase_after_prefix (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (ω : Sample) (a : ℕ) (pre inside tail : List ℕ) (s : Option ℕ)
    (ha : x + position ω a ∈ K)
    (hin : ∀ i ∈ inside, x + position ω i ∈ C) :
    scanChildIntervals K C x ω s (pre ++ a :: (inside ++ tail)) =
      scanChildIntervals K C x ω s (pre ++ a :: tail) := by
  induction pre generalizing s with
  | nil => exact scanChildIntervals_erase_after_entrance K C hKC x ω a inside tail s ha hin
  | cons i pre ih =>
    cases s with
    | none =>
      by_cases hi : x + position ω i ∈ K
      · simpa only [List.cons_append, scanChildIntervals, if_pos hi] using ih (some i)
      · simpa only [List.cons_append, scanChildIntervals, if_neg hi] using ih none
    | some b =>
      by_cases hi : x + position ω i ∈ C
      · simpa only [List.cons_append, scanChildIntervals, not_not.mpr hi, if_false] using
          ih (some b)
      · simpa only [List.cons_append, scanChildIntervals, if_pos hi] using
          congrArg (List.cons (b, i)) (ih none)

end SRWTightness
