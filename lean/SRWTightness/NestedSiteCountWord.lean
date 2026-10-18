import SRWTightness.SiteExcursionWeightRange

namespace SRWTightness

/-- Site-word counting agrees with the original recursively extracted direction-word records. -/
theorem nestedSiteCount_word (levels : List (Finset Site × Finset Site))
    (x : Site) (w : PathWord) :
    nestedSiteCount levels (wordSiteObservations x w) =
      (terminalWordRecords levels x w).length := by
  induction levels generalizing x w with
  | nil => rfl
  | cons level levels ih =>
    rcases level with ⟨K, C⟩
    rw [nestedSiteCount, wordSiteObservations_eq_range]
    have hh := siteExcursionWeight_scan_range K C x (wordPath w)
      (nestedSiteCount levels) (w.length + 1) 0 none (by intro a he; cases he)
    simp only [Option.map_none] at hh
    rw [hh]
    simp only [terminalWordRecords, List.length_flatMap, wordChildIntervals,
      List.range_eq_range']
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    have he := wordSiteObservations_slice x w q.1 q.2
    change wordSiteObservations _ _ = siteObservationRange _ _ _ _ at he
    rw [← he]
    exact ih _ _

end SRWTightness
