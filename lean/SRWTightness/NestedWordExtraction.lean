import SRWTightness.WordChildListOccupation

namespace SRWTightness

/-- Recursively retain all terminal child words and their actual starting sites, with multiplicity. -/
def terminalWordRecords : List (Finset Site × Finset Site) → Site → PathWord → List (Site × PathWord)
  | [], x, w => [(x, w)]
  | (K, C) :: levels, x, w =>
      (wordChildIntervals K C x w).flatMap (fun q ↦
        terminalWordRecords levels (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2))

/-- The visit count carried by a finite record with its actual starting site. -/
def wordRecordVisits (y : Site) (r : Site × PathWord) : ℕ :=
  localTime (wordPath r.2) r.2.length (y - r.1)

/-- Sufficient nesting and observation conditions at every recursive level. -/
def NestedWordDomains (y : Site) : Finset Site → List (Finset Site × Finset Site) → Prop
  | _, [] => True
  | D, (K, C) :: levels => y ∈ K ∧ K ⊆ C ∧ C ⊆ D ∧ NestedWordDomains y C levels

/-- Recursive terminal words preserve the full occupation count of the parent word. -/
theorem terminalWordRecords_visit_sum (levels : List (Finset Site × Finset Site))
    (D : Finset Site) (y : Site) (hn : NestedWordDomains y D levels)
    (x : Site) (w : PathWord) (hend : x + position (wordPath w) w.length ∉ D) :
    ((terminalWordRecords levels x w).map (wordRecordVisits y)).sum =
      localTime (wordPath w) w.length (y - x) := by
  induction levels generalizing D x w with
  | nil => simp [terminalWordRecords, wordRecordVisits]
  | cons level levels ih =>
    obtain ⟨K, C⟩ := level
    obtain ⟨hy, hKC, hCD, htail⟩ := hn
    have hout : x + position (wordPath w) w.length ∉ C := fun h ↦ hend (hCD h)
    rw [wordLocalTime_child_list K C hKC x y hy w hout]
    simp only [terminalWordRecords, List.map_flatMap, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    exact ih C htail _ _ (wordChildIntervals_slice_endpoint K C x w q hq)

end SRWTightness
