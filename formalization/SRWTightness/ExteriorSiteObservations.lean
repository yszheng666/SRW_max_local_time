import SRWTightness.ExteriorPathRecord
import SRWTightness.SiteObservationRange

namespace SRWTightness

/-- Observed exterior pieces, with a jump from each retained entrance to its stored exit. -/
def exteriorSiteObservations : Site → ExteriorPathRecord → List Site
  | x, ([], tail) => wordSiteObservations x tail
  | x, (slot :: slots, tail) =>
      wordSiteObservations x slot.1 ++ exteriorSiteObservations slot.2.2.2 (slots, tail)

/-- Position ranges retained by a chronological list of deleted internal intervals. -/
def packedSiteObservations (x : Site) (w : PathWord) :
    ℕ → List (ℕ × ℕ) → List Site
  | previous, [] => siteObservationRange x (wordPath w) previous (w.length - previous + 1)
  | previous, (a, b) :: intervals =>
      siteObservationRange x (wordPath w) previous (a - previous + 1) ++
        packedSiteObservations x w b intervals

/-- The exterior record determines its complete compressed site list exactly. -/
theorem exteriorSiteObservations_pack (label : Site → Bool) (x : Site) (w : PathWord)
    (intervals : List (ℕ × ℕ)) (previous : ℕ) :
    exteriorSiteObservations (x + position (wordPath w) previous)
      (packExteriorRecord label x w previous intervals) =
        packedSiteObservations x w previous intervals := by
  induction intervals generalizing previous with
  | nil =>
    simpa only [exteriorSiteObservations, packExteriorRecord, packedSiteObservations,
      siteObservationRange] using wordSiteObservations_slice x w previous w.length
  | cons q intervals ih =>
    rcases q with ⟨a, b⟩
    simp only [packExteriorRecord, exteriorSiteObservations, packedSiteObservations, ih]
    rw [wordSiteObservations_slice]
    rfl

end SRWTightness
