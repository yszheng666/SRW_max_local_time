import SRWTightness.WordSiteObservations

namespace SRWTightness

/-- A consecutive finite list of positions on an arbitrary walk. -/
def siteObservationRange (x : Site) (ω : Sample) (a n : ℕ) : List Site :=
  (List.range' a n).map (fun i ↦ x + position ω i)

/-- The next chronological observation appends to the finite position range. -/
theorem siteObservationRange_snoc (x : Site) (ω : Sample) (a start : ℕ) (ha : a ≤ start) :
    siteObservationRange x ω a (start - a) ++ [x + position ω start] =
      siteObservationRange x ω a (start + 1 - a) := by
  have he : start + 1 - a = (start - a) + 1 := by omega
  rw [he]
  unfold siteObservationRange
  rw [List.range'_concat, List.map_append, List.map_singleton]
  simp only [Nat.one_mul]
  have hh : a + (start - a) = start := by omega
  rw [hh]

/-- Inclusive word observations agree with the chronological range from zero. -/
theorem wordSiteObservations_eq_range (x : Site) (w : PathWord) :
    wordSiteObservations x w = siteObservationRange x (wordPath w) 0 (w.length + 1) := by
  simp [wordSiteObservations, siteObservationRange, List.range_eq_range']

end SRWTightness
