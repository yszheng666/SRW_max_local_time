import SRWTightness.LabeledRootCountMixture

open scoped BigOperators
namespace SRWTightness

/-- Reattaching headers to their projected records preserves the same chronological pairs. -/
theorem header_zip_record_map {α β γ δ : Type*} (ss : List α) (us : List β)
    (F : α → β → γ) (G : α → γ → δ) :
    (ss.zip ((ss.zip us).map (fun p ↦ F p.1 p.2))).map (fun p ↦ G p.1 p.2) =
      (ss.zip us).map (fun p ↦ G p.1 (F p.1 p.2)) := by
  induction ss generalizing us with
  | nil => simp
  | cons s ss ih =>
    cases us with
    | nil => simp
    | cons u us => simp only [List.zip_cons_cons, List.map_cons, ih]

/-- A specified count tuple determines both labeled totals without referring to any independence. -/
theorem exterior_count_total_of_tuple (h : ExteriorPathRecord) (us : List PathWord)
    (F : ExteriorSlot → PathWord → ℕ) (r : Fin h.1.length → ℕ)
    (hr : (h.1.zip us).map (fun p ↦ F p.1 p.2) = List.ofFn r) (c : Bool) :
    labeledRootTotal (fun i ↦ (h.1.get i).2.1) r c =
      ((h.1.zip us).map (fun p ↦ if p.1.2.1 = c then F p.1 p.2 else 0)).sum := by
  calc
    _ = ((h.1.zip (List.ofFn r)).map (fun p ↦ if p.1.2.1 = c then p.2 else 0)).sum := by
      rw [list_zip_ofFn_map h.1 r (fun s v ↦ if s.2.1 = c then v else 0)]
      simp only [List.sum_ofFn, labeledRootTotal]
    _ = ((h.1.zip ((h.1.zip us).map (fun p ↦ F p.1 p.2))).map
        (fun p ↦ if p.1.2.1 = c then p.2 else 0)).sum := by rw [hr]
    _ = _ := congrArg List.sum (header_zip_record_map h.1 us F
      (fun s v ↦ if s.2.1 = c then v else 0))

end SRWTightness
