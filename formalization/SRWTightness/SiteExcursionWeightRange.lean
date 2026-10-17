import SRWTightness.SiteObservationRange
import SRWTightness.NestedSiteCount

namespace SRWTightness

/-- The site-list scanner and the original interval scanner give identical weighted records. -/
theorem siteExcursionWeight_scan_range (K C : Finset Site) (x : Site) (ω : Sample)
    (weight : List Site → ℕ) (n start : ℕ) (s : Option ℕ)
    (hs : ∀ a, s = some a → a ≤ start) :
    siteExcursionWeight K C weight
      (s.map (fun a ↦ siteObservationRange x ω a (start - a)))
      (siteObservationRange x ω start n) =
    ((scanChildIntervals K C x ω s (List.range' start n)).map
      (fun q ↦ weight (siteObservationRange x ω q.1 (q.2 - q.1 + 1)))).sum := by
  induction n generalizing start s with
  | zero => simp [siteObservationRange, siteExcursionWeight, scanChildIntervals]
  | succ n ih =>
    have hr : siteObservationRange x ω start (n + 1) =
        (x + position ω start) :: siteObservationRange x ω (start + 1) n := by
      simp [siteObservationRange, List.range'_succ]
    rw [hr, List.range'_succ]
    cases s with
    | none =>
      by_cases hi : x + position ω start ∈ K
      · have hh := ih (start + 1) (some start) (by intro a he; cases he; omega)
        simpa [siteExcursionWeight, scanChildIntervals, hi, siteObservationRange,
          Nat.add_sub_cancel_left] using hh
      · simpa only [Option.map_none, siteExcursionWeight, scanChildIntervals, if_neg hi] using
          ih (start + 1) none (by intro a he; cases he)
    | some a =>
      have ha : a ≤ start := hs a rfl
      by_cases hi : x + position ω start ∈ C
      · have hh := ih (start + 1) (some a) (by intro b he; cases he; omega)
        simpa only [Option.map_some, siteExcursionWeight, scanChildIntervals,
          if_pos hi, not_not.mpr hi, if_false, siteObservationRange_snoc x ω a start ha] using hh
      · have hh := ih (start + 1) none (by intro b he; cases he)
        simp only [Option.map_some, siteExcursionWeight, scanChildIntervals, if_neg hi,
          if_pos hi, List.map_cons, List.sum_cons, Option.map_none,
          siteObservationRange_snoc x ω a start ha]
        have he : start + 1 - a = start - a + 1 := by omega
        simp only [Option.map_none] at hh
        rw [he, hh]

end SRWTightness
