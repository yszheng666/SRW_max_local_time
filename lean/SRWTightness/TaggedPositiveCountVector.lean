import SRWTightness.TaggedBlockCounts

namespace SRWTightness

/-- The exact positive block-count vector of a compatible tuple with its prescribed two totals. -/
noncomputable def orderedTaggedRootVector {α β : Type*} (n : ℕ) (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) (hr : orderedTaggedCompatible label r)
    (k l : ℕ) (hk : (orderedTaggedForests r).1.length = k)
    (hl : (orderedTaggedForests r).2.length = l) : Fin n → Fin (k + l + 1) :=
  fun i ↦ ⟨taggedBlockLength (r i), Nat.lt_succ_iff.mpr
    (ordered_tagged_block_count_bound n label r hr k l hk hl i)⟩

/-- The bounded vector retains every original block length exactly. -/
theorem ordered_tagged_root_vector_value {α β : Type*} (n : ℕ) (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) (hr : orderedTaggedCompatible label r)
    (k l : ℕ) (hk : (orderedTaggedForests r).1.length = k)
    (hl : (orderedTaggedForests r).2.length = l) (i : Fin n) :
    (orderedTaggedRootVector n label r hr k l hk hl i).val = taggedBlockLength (r i) := rfl

/-- The original finite positive-count index contains the actual compatible tuple's vector. -/
theorem ordered_tagged_root_vector_mem {α β : Type*} (n : ℕ) (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) (hr : orderedTaggedCompatible label r)
    (k l : ℕ) (hk : (orderedTaggedForests r).1.length = k)
    (hl : (orderedTaggedForests r).2.length = l) :
    orderedTaggedRootVector n label r hr k l hk hl ∈ positiveRootVectors label k l := by
  classical
  simp only [positiveRootVectors, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ i, 0 < taggedBlockLength (r i)) ∧
    labeledRootTotal label (fun i ↦ taggedBlockLength (r i)) false = k ∧
      labeledRootTotal label (fun i ↦ taggedBlockLength (r i)) true = l
  have hc := (ordered_tagged_compatible_counts n label r).mp hr
  have ht := ordered_tagged_forest_length_totals n label r hr
  exact ⟨fun i ↦ (hc i).2, ht.1.symm.trans hk, ht.2.symm.trans hl⟩

/-- A bounded vector matching the tuple's block lengths is necessarily its exact count vector. -/
theorem ordered_tagged_root_vector_unique {α β : Type*} (n : ℕ) (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) (hr : orderedTaggedCompatible label r)
    (k l : ℕ) (hk : (orderedTaggedForests r).1.length = k)
    (hl : (orderedTaggedForests r).2.length = l) (s : Fin n → Fin (k + l + 1))
    (hs : ∀ i, (s i).val = taggedBlockLength (r i)) :
    s = orderedTaggedRootVector n label r hr k l hk hl := by
  funext i
  exact Fin.ext (hs i)

end SRWTightness
