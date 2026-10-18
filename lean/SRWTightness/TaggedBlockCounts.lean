import SRWTightness.OrderedTaggedForestMixture

open scoped BigOperators

namespace SRWTightness

/-- The prescribed site tag read from an actual ordered block. -/
def taggedBlockLabel {α β : Type*} (r : Sum (List α) (List β)) : Bool :=
  r.elim (fun _ ↦ false) (fun _ ↦ true)

/-- The number of ordered roots in an actual tagged block. -/
def taggedBlockLength {α β : Type*} (r : Sum (List α) (List β)) : ℕ :=
  r.elim List.length List.length

/-- Compatibility means the exact prescribed tag and a strictly positive root count at every
slot. -/
theorem ordered_tagged_compatible_counts {α β : Type*} (n : ℕ) (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) :
    orderedTaggedCompatible label r ↔
      ∀ i, taggedBlockLabel (r i) = label i ∧ 0 < taggedBlockLength (r i) := by
  unfold orderedTaggedCompatible
  apply forall_congr'
  intro i
  cases r i with
  | inl rs =>
    change (label i = false ∧ rs ≠ []) ↔ (false = label i ∧ 0 < rs.length)
    constructor
    · rintro ⟨hl, hn⟩
      exact ⟨hl.symm, List.length_pos_iff_ne_nil.mpr hn⟩
    · rintro ⟨hl, hn⟩
      exact ⟨hl.symm, List.length_pos_iff_ne_nil.mp hn⟩
  | inr rs =>
    change (label i = true ∧ rs ≠ []) ↔ (true = label i ∧ 0 < rs.length)
    constructor
    · rintro ⟨hl, hn⟩
      exact ⟨hl.symm, List.length_pos_iff_ne_nil.mpr hn⟩
    · rintro ⟨hl, hn⟩
      exact ⟨hl.symm, List.length_pos_iff_ne_nil.mp hn⟩


/-- Compatible block lengths give the two original concatenated forest root totals. -/
theorem ordered_tagged_forest_length_totals {α β : Type*} (n : ℕ) (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) (hr : orderedTaggedCompatible label r) :
    (orderedTaggedForests r).1.length =
      labeledRootTotal label (fun i ↦ taggedBlockLength (r i)) false ∧
      (orderedTaggedForests r).2.length =
        labeledRootTotal label (fun i ↦ taggedBlockLength (r i)) true := by
  constructor
  · simp only [orderedTaggedForests, taggedForestLeft, List.length_flatMap,
      List.map_ofFn, List.sum_ofFn]
    unfold labeledRootTotal
    apply Finset.sum_congr rfl
    intro i _
    have hi := hr i
    cases hri : r i with
    | inl rs =>
      have hlabel : label i = false := (by simpa [hri] using hi : label i = false ∧ rs ≠ []).1
      simp [hri, taggedBlockLength, hlabel]
    | inr rs =>
      have hlabel : label i = true := (by simpa [hri] using hi : label i = true ∧ rs ≠ []).1
      simp [hri, taggedBlockLength, hlabel]
  · simp only [orderedTaggedForests, taggedForestRight, List.length_flatMap,
      List.map_ofFn, List.sum_ofFn]
    unfold labeledRootTotal
    apply Finset.sum_congr rfl
    intro i _
    have hi := hr i
    cases hri : r i with
    | inl rs =>
      have hlabel : label i = false := (by simpa [hri] using hi : label i = false ∧ rs ≠ []).1
      simp [hri, taggedBlockLength, hlabel]
    | inr rs =>
      have hlabel : label i = true := (by simpa [hri] using hi : label i = true ∧ rs ≠ []).1
      simp [hri, taggedBlockLength, hlabel]

/-- Every compatible block count fits in the original bounded vector box. -/
theorem ordered_tagged_block_count_bound {α β : Type*} (n : ℕ) (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) (hr : orderedTaggedCompatible label r)
    (k l : ℕ) (hk : (orderedTaggedForests r).1.length = k)
    (hl : (orderedTaggedForests r).2.length = l) (i : Fin n) :
    taggedBlockLength (r i) ≤ k + l := by
  have ht := ordered_tagged_forest_length_totals n label r hr
  have hs : (∑ j, taggedBlockLength (r j)) = k + l := by
    rw [← labeled_root_total_partition label (fun j ↦ taggedBlockLength (r j)),
      ← ht.1, ← ht.2, hk, hl]
  calc
    _ ≤ ∑ j, taggedBlockLength (r j) :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    _ = k + l := hs

end SRWTightness
