import Mathlib.Data.List.Basic

namespace SRWTightness

/-- Deleting segments with empty records preserves the complete chronological forest. -/
theorem flatMap_filter_of_empty {α β : Type*} (xs : List α) (label : α → Bool)
    (F : α → List β) (h : ∀ x ∈ xs, label x = false → F x = []) :
    xs.flatMap F = (xs.filter label).flatMap F := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy ↦ h y (List.mem_cons_of_mem x hy))
    cases hl : label x
    · have hx := h x List.mem_cons_self hl
      simp [hl, hx, ih']
    · simp [hl, ih']

/-- Empty opposite-label lists identify both full forests with their own-label segment partitions. -/
theorem two_label_forest_partition {α β γ : Type*} (xs : List α) (label : α → Bool)
    (F₀ : α → List β) (F₁ : α → List γ)
    (h₀ : ∀ x ∈ xs, label x = true → F₀ x = [])
    (h₁ : ∀ x ∈ xs, label x = false → F₁ x = []) :
    xs.flatMap F₀ = (xs.filter (fun x ↦ !(label x))).flatMap F₀ ∧
    xs.flatMap F₁ = (xs.filter label).flatMap F₁ := by
  refine ⟨flatMap_filter_of_empty xs (fun x ↦ !(label x)) F₀ ?_,
    flatMap_filter_of_empty xs label F₁ h₁⟩
  intro x hx hl
  apply h₀ x hx
  simpa using hl

end SRWTightness
