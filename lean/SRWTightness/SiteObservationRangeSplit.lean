import SRWTightness.SiteObservationRange

namespace SRWTightness

/-- Consecutive position ranges split at an intermediate time without duplicating that time. -/
theorem siteObservationRange_split (x : Site) (ω : Sample) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    siteObservationRange x ω a (c - a) =
      siteObservationRange x ω a (b - a) ++ siteObservationRange x ω b (c - b) := by
  unfold siteObservationRange
  rw [← List.map_append]
  have he : a + (b - a) = b := by omega
  have hn : (b - a) + (c - b) = c - a := by omega
  have hh := List.range'_append_1 (s := a) (m := b - a) (n := c - b)
  rw [he, hn] at hh
  exact congrArg (List.map (fun i ↦ x + position ω i)) hh.symm

/-- A positive-length position range starts with its first observation. -/
theorem siteObservationRange_cons (x : Site) (ω : Sample) (a b : ℕ) (hab : a < b) :
    siteObservationRange x ω a (b - a) =
      (x + position ω a) :: siteObservationRange x ω (a + 1) (b - (a + 1)) := by
  have he : b - a = (b - (a + 1)) + 1 := by omega
  rw [he]
  simp [siteObservationRange, List.range'_succ]

end SRWTightness
