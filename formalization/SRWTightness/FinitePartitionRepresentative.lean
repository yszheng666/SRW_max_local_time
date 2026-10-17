import Mathlib.Data.Finset.Card

namespace SRWTightness

/-- Select one member of each nonempty finite partition cell, with a fixed default elsewhere. -/
noncomputable def finitePartitionRepresentative {ι κ : Type*}
    (J : Finset ι) (f : ι → κ) (o : ι) (e : κ) : ι := by
  classical
  exact if h : ∃ x ∈ J, f x = e then Classical.choose h else o

/-- A nonempty cell representative belongs to the original set and has the prescribed label. -/
theorem finitePartitionRepresentative_spec {ι κ : Type*}
    (J : Finset ι) (f : ι → κ) (o : ι) (e : κ) (he : ∃ x ∈ J, f x = e) :
    finitePartitionRepresentative J f o e ∈ J ∧
      f (finitePartitionRepresentative J f o e) = e := by
  classical
  simp only [finitePartitionRepresentative, dif_pos he]
  exact Classical.choose_spec he

/-- The number of selected representatives is bounded by the number of possible cell labels. -/
theorem finitePartitionRepresentative_card_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (J : Finset ι) (f : ι → κ) (o : ι) (E : Finset κ)
    (hE : ∀ x ∈ J, f x ∈ E) :
    (J.image (fun x ↦ finitePartitionRepresentative J f o (f x))).card ≤ E.card := by
  have he : J.image f ⊆ E := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact hE x hx
  change (J.image (finitePartitionRepresentative J f o ∘ f)).card ≤ E.card
  rw [← Finset.image_image]
  exact (Finset.card_image_le).trans (Finset.card_le_card he)

end SRWTightness
