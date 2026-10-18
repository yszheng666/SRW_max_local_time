import SRWTightness.ExteriorWordReassembly

namespace SRWTightness

/-- The total number of increments retained in the exterior pieces. -/
def exteriorWordLength (h : ExteriorPathRecord) : ℕ :=
  (h.1.map (fun slot ↦ slot.1.length)).sum + h.2.length

/-- Reinsertion adds exactly the lengths of the supplied internal words. -/
theorem reassembleExteriorWord_length (h : ExteriorPathRecord) (us : List PathWord)
    (hlen : us.length = h.1.length) :
    (reassembleExteriorWord h us).length =
      exteriorWordLength h + (us.map PathWord.length).sum := by
  rcases h with ⟨slots, tail⟩
  induction slots generalizing us with
  | nil =>
    have hu : us = [] := List.length_eq_zero_iff.mp hlen
    subst us
    simp [reassembleExteriorWord, exteriorWordLength]
  | cons slot slots ih =>
    cases us with
    | nil => simp at hlen
    | cons u us =>
      have hl : us.length = slots.length := by simpa using hlen
      simp only [reassembleExteriorWord, pathWordAppend_length, exteriorWordLength,
        List.map_cons, List.sum_cons]
      have hh := ih us hl
      unfold exteriorWordLength at hh
      dsimp only at hh
      omega

/-- The actual path length splits into retained exterior and complete internal lengths. -/
theorem pathWord_length_exterior_internal (K C : Finset Site) (label : Site → Bool)
    (x : Site) (w : PathWord) :
    w.length = exteriorWordLength (wordExteriorRecord K C label x w) +
      ((wordChildRecords K C x (fun _ u ↦ u) w).map PathWord.length).sum := by
  have hh := reassembleExteriorWord_length (wordExteriorRecord K C label x w)
    (wordChildRecords K C x (fun _ u ↦ u) w) (by
      simp [wordChildRecords, wordExteriorRecord, packExteriorRecord_length])
  rwa [reassembleExteriorWord_actual] at hh

end SRWTightness
