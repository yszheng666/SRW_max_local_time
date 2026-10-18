import SRWTightness.WordChildCoverage
import SRWTightness.ActualChildRecords

namespace SRWTightness

/-- A word starting in its target and ending outside its domain contains a complete child record. -/
theorem word_child_records_nonempty {M : Type*} (K C : Finset Site) (hKC : K ⊆ C)
    (x : Site) (w : PathWord) (hx : x ∈ K)
    (hend : x + position (wordPath w) w.length ∉ C) (F : Site → PathWord → M) :
    wordChildRecords K C x F w ≠ [] := by
  have hw : 0 < w.length := by
    by_contra h
    have hz : w.length = 0 := by omega
    have hh := hKC hx
    apply hend
    simpa only [hz, position_zero_as_zero, add_zero] using hh
  obtain ⟨q, hq, _⟩ := wordChildIntervals_cover_visit K C hKC x w hend 0 hw (by simpa using hx)
  have hm : F (x + position (wordPath w) q.1) (slicePathWord w q.1 q.2) ∈
      wordChildRecords K C x F w := List.mem_map.mpr ⟨q, hq, rfl⟩
  intro he
  simpa only [he, List.not_mem_nil] using hm

/-- Each segment contributes at least one root at one of the two sites. -/
theorem list_length_le_two_root_totals {ι α β : Type*} (xs : List ι)
    (F : ι → List α) (G : ι → List β)
    (h : ∀ x ∈ xs, F x ≠ [] ∨ G x ≠ []) :
    xs.length ≤ (xs.flatMap F).length + (xs.flatMap G).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hr := ih (fun y hy ↦ h y (by simp [hy]))
    have hp : 1 ≤ (F x).length + (G x).length := by
      rcases h x (by simp) with hx | hx
      · have hh := List.length_pos_iff.mpr hx
        omega
      · have hh := List.length_pos_iff.mpr hx
        omega
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

/-- The number of complete union-long segments is bounded by the two grouped short-root totals. -/
theorem word_long_segment_count (K₀ C₀ K₁ C₁ C : Finset Site)
    (hK₀ : K₀ ⊆ C₀) (hK₁ : K₁ ⊆ C₁) (hC₀ : C₀ ⊆ C) (hC₁ : C₁ ⊆ C)
    (x : Site) (w : PathWord) :
    (wordChildIntervals (K₀ ∪ K₁) C x w).length ≤
      ((wordChildRecords (K₀ ∪ K₁) C x
        (fun y u ↦ wordChildRecords K₀ C₀ y (fun z v ↦ (z, v)) u) w).flatten).length +
      ((wordChildRecords (K₀ ∪ K₁) C x
        (fun y u ↦ wordChildRecords K₁ C₁ y (fun z v ↦ (z, v)) u) w).flatten).length := by
  have hh := list_length_le_two_root_totals (wordChildIntervals (K₀ ∪ K₁) C x w)
    (fun q ↦ wordChildRecords K₀ C₀ (x + position (wordPath w) q.1)
      (fun z v ↦ (z, v)) (slicePathWord w q.1 q.2))
    (fun q ↦ wordChildRecords K₁ C₁ (x + position (wordPath w) q.1)
      (fun z v ↦ (z, v)) (slicePathWord w q.1 q.2)) (by
        intro q hq
        have hin := (wordChildIntervals_endpoints (K₀ ∪ K₁) C x w q hq).1
        have hout := wordChildIntervals_slice_endpoint (K₀ ∪ K₁) C x w q hq
        rcases Finset.mem_union.mp hin with hin | hin
        · exact Or.inl (word_child_records_nonempty K₀ C₀ hK₀ _ _ hin
            (fun h ↦ hout (hC₀ h)) _)
        · exact Or.inr (word_child_records_nonempty K₁ C₁ hK₁ _ _ hin
            (fun h ↦ hout (hC₁ h)) _))
  simpa only [List.flatMap_def, wordChildRecords] using hh

end SRWTightness
