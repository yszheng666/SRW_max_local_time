import SRWTightness.SourceExteriorRecordForests

namespace SRWTightness

/-- Tagged block errors split into the common count cost and the two ordered fine-forest costs. -/
theorem source_tagged_error_decomposition (A C B W t a₀ a₁ : ℝ)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (rs : List (SourceExteriorFineValue t K₀ K₁ ν)) :
    (rs.map (sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J)).sum =
      A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) * (rs.length : ℝ) +
      C * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14) *
        (((taggedForestLeft rs).length : ℝ) + (taggedForestRight rs).length) +
      ((taggedForestLeft rs).map (sourceLongFineError B W t a₀ K₀ ν)).sum +
      ((taggedForestRight rs).map (sourceLongFineError B W t a₁ K₁ ν)).sum := by
  induction rs with
  | nil => simp [taggedForestLeft, taggedForestRight]
  | cons r rs ih =>
    cases r with
    | inl us =>
      simp only [List.map_cons, List.sum_cons, sourceExteriorFineError, Sum.elim_inl,
        sourceLongFineListError, taggedForestLeft, taggedForestRight, List.flatMap_cons,
        Sum.elim_inl, id_eq, List.nil_append, List.length_cons, List.length_append,
        Nat.cast_add, Nat.cast_one, List.map_append, List.sum_append] at ih ⊢
      rw [ih]
      ring
    | inr us =>
      simp only [List.map_cons, List.sum_cons, sourceExteriorFineError, Sum.elim_inr,
        sourceLongFineListError, taggedForestLeft, taggedForestRight, List.flatMap_cons,
        Sum.elim_inr, id_eq, List.nil_append, List.length_cons, List.length_append,
        Nat.cast_add, Nat.cast_one, List.map_append, List.sum_append] at ih ⊢
      rw [ih]
      ring

/-- Each nonempty tagged block contributes at least one root to the two concatenated forests. -/
theorem tagged_forest_slots_le_roots {α β : Type*} (rs : List (Sum (List α) (List β)))
    (hr : ∀ r ∈ rs, r.elim (fun us ↦ us ≠ []) (fun us ↦ us ≠ [])) :
    rs.length ≤ (taggedForestLeft rs).length + (taggedForestRight rs).length := by
  induction rs with
  | nil => simp [taggedForestLeft, taggedForestRight]
  | cons r rs ih =>
    have ht := ih (fun q hq ↦ hr q (List.mem_cons_of_mem r hq))
    have hh := hr r List.mem_cons_self
    cases r with
    | inl us =>
      have hu : 0 < us.length := List.length_pos_iff.mpr hh
      simp only [taggedForestLeft, taggedForestRight, List.flatMap_cons, Sum.elim_inl,
        id_eq, List.nil_append, List.length_cons, List.length_append] at ht ⊢
      omega
    | inr us =>
      have hu : 0 < us.length := List.length_pos_iff.mpr hh
      simp only [taggedForestLeft, taggedForestRight, List.flatMap_cons, Sum.elim_inr,
        id_eq, List.nil_append, List.length_cons, List.length_append] at ht ⊢
      omega

end SRWTightness
