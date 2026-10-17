import SRWTightness.ExteriorPathRecord

namespace SRWTightness

/-- Erased headers and their internal words retain the same entrances in chronological order. -/
theorem pack_exterior_word_alignment {M : Type*} (label : Site → Bool) (x : Site)
    (w : PathWord) (intervals : List (ℕ × ℕ)) (previous : ℕ) (F : Site → PathWord → M) :
    (((packExteriorRecord label x w previous intervals).1.zip
      (intervals.map (fun q ↦ slicePathWord w q.1 q.2))).map
      (fun p ↦ F p.1.2.2.1 p.2)) =
      intervals.map (fun q ↦ F (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2)) := by
  induction intervals generalizing previous with
  | nil => rfl
  | cons q qs ih =>
    rcases q with ⟨a, b⟩
    simp only [packExteriorRecord, List.map_cons, List.zip_cons_cons, ih]

/-- Zipping actual exterior headers with internal words reconstructs every deterministic child record. -/
theorem killed_exterior_word_alignment {M : Type*} (D K C : Finset Site)
    (label : Site → Bool) (x : Site) (ω : Sample) (F : Site → PathWord → M) :
    (((killedExteriorRecord D K C label x ω).1.zip
      (killedChildRecords D K C x (fun _ u ↦ u) ω)).map
      (fun p ↦ F p.1.2.2.1 p.2)) = killedChildRecords D K C x F ω := by
  exact pack_exterior_word_alignment label x (killedPathWord D x ω)
    (wordChildIntervals K C x (killedPathWord D x ω)) 0 F

/-- On an actual exterior/word fiber, all finer records are recovered from that fiber's fixed data. -/
theorem exterior_word_fiber_records {M : Type*} (D K C : Finset Site)
    (label : Site → Bool) (x : Site) (ω : Sample) (h : ExteriorPathRecord) (us : List PathWord)
    (hh : killedExteriorRecord D K C label x ω = h)
    (hu : killedChildRecords D K C x (fun _ u ↦ u) ω = us) (F : Site → PathWord → M) :
    (h.1.zip us).map (fun p ↦ F p.1.2.2.1 p.2) = killedChildRecords D K C x F ω := by
  rw [← hh, ← hu]
  exact killed_exterior_word_alignment D K C label x ω F

end SRWTightness
