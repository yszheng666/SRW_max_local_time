import SRWTightness.ExteriorPathRecord
import SRWTightness.ChildSliceAdmissible

namespace SRWTightness

/-- Exterior headers remain paired with the endpoints of their actual admissible internal words. -/
theorem packExteriorRecord_words_admissible (C : Finset Site) (label : Site → Bool)
    (x : Site) (w : PathWord) (intervals : List (ℕ × ℕ)) (previous : ℕ)
    (hi : ∀ q ∈ intervals, AdmissibleExitWord C (x + position (wordPath w) q.1)
      (x + position (wordPath w) q.2) (slicePathWord w q.1 q.2)) :
    ∀ pair ∈ (packExteriorRecord label x w previous intervals).1.zip
      (intervals.map (fun q ↦ slicePathWord w q.1 q.2)),
      AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2 := by
  induction intervals generalizing previous with
  | nil => simp [packExteriorRecord]
  | cons q intervals ih =>
    rcases q with ⟨a, b⟩
    intro pair hp
    simp only [packExteriorRecord, List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with he | hp
    · subst pair
      exact hi (a, b) List.mem_cons_self
    · exact ih b (fun q hq ↦ hi q (List.mem_cons_of_mem (a, b) hq)) pair hp

/-- The complete internal word list always satisfies every recorded prescribed-exit constraint. -/
theorem wordExteriorRecord_words_admissible (K C : Finset Site) (hKC : K ⊆ C)
    (label : Site → Bool) (x : Site) (w : PathWord) :
    ∀ pair ∈ (wordExteriorRecord K C label x w).1.zip
      (wordChildRecords K C x (fun _ u ↦ u) w),
      AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2 := by
  exact packExteriorRecord_words_admissible C label x w (wordChildIntervals K C x w) 0
    (fun q hq ↦ wordChildIntervals_slice_admissible K C hKC x w q hq)

end SRWTightness
