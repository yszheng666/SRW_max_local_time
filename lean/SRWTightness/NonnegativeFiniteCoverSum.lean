import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

open scoped BigOperators
namespace SRWTightness

/-- Nonnegative weights may be overcounted on overlapping finite sets. -/
theorem nonnegative_union_sum_le {α : Type*} [DecidableEq α]
    (s t : Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s ∪ t, f x) ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have he := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hn : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg (fun x _ ↦ hf x)
  linarith only [he, hn]

/-- A finite family of sets bounds the weight of its union, without disjointness assumptions. -/
theorem nonnegative_biUnion_sum_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (sets : α → Finset β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion sets, f x) ≤ ∑ i ∈ s, ∑ x ∈ sets i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (nonnegative_union_sum_le (sets i) (s.biUnion sets) f hf).trans
      (add_le_add (le_refl _) ih)

/-- A cover by five finite sets gives the corresponding five-term sum bound. -/
theorem nonnegative_five_cover_sum_le {α : Type*} [DecidableEq α]
    (s s₁ s₂ s₃ s₄ s₅ : Finset α) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hcover : ∀ x ∈ s, x ∈ s₁ ∨ x ∈ s₂ ∨ x ∈ s₃ ∨ x ∈ s₄ ∨ x ∈ s₅) :
    (∑ x ∈ s, f x) ≤ (∑ x ∈ s₁, f x) + (∑ x ∈ s₂, f x) +
      (∑ x ∈ s₃, f x) + (∑ x ∈ s₄, f x) + ∑ x ∈ s₅, f x := by
  have hsub : s ⊆ (((s₁ ∪ s₂) ∪ s₃) ∪ s₄) ∪ s₅ := by
    intro x hx
    rcases hcover x hx with h | h | h | h | h <;> simp [h]
  have h₁ := nonnegative_union_sum_le s₁ s₂ f hf
  have h₂ := nonnegative_union_sum_le (s₁ ∪ s₂) s₃ f hf
  have h₃ := nonnegative_union_sum_le ((s₁ ∪ s₂) ∪ s₃) s₄ f hf
  have h₄ := nonnegative_union_sum_le (((s₁ ∪ s₂) ∪ s₃) ∪ s₄) s₅ f hf
  have h₀ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ ↦ hf x)
  linarith only [h₀, h₁, h₂, h₃, h₄]

end SRWTightness
