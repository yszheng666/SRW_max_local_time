import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

universe u

namespace SRWTightness

/-- Selecting one site's nonnegative error in each segment is bounded by charging both sites. -/
theorem selected_segment_error_bound {α : Type*} (xs : List α) (label : α → Bool)
    (δ ε : ℝ) (n₀ n₁ : α → ℕ) (e₀ e₁ : α → ℝ) (hε : 0 ≤ ε)
    (h₀ : ∀ x ∈ xs, 0 ≤ e₀ x) (h₁ : ∀ x ∈ xs, 0 ≤ e₁ x) :
    (xs.map (fun x ↦ δ + ε * (if label x then (n₁ x : ℝ) else (n₀ x : ℝ)) +
      (if label x then e₁ x else e₀ x))).sum ≤
      δ * (xs.length : ℝ) + ε * ((xs.map (fun x ↦ (n₀ x : ℝ))).sum +
        (xs.map (fun x ↦ (n₁ x : ℝ))).sum) + (xs.map e₀).sum + (xs.map e₁).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy ↦ h₀ y (List.mem_cons_of_mem x hy))
      (fun y hy ↦ h₁ y (List.mem_cons_of_mem x hy))
    have hx₀ := h₀ x (List.mem_cons_self)
    have hx₁ := h₁ x (List.mem_cons_self)
    have hn₀ : 0 ≤ ε * (n₀ x : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
    have hn₁ : 0 ≤ ε * (n₁ x : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
    cases hl : label x <;>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, hl, Bool.false_eq_true, ↓reduceIte] <;> nlinarith

/-- The selected local comparison costs are bounded by the two flattened fine forests. -/
theorem selected_forest_error_bound {α β γ : Type u} (xs : List α) (label : α → Bool)
    (δ ε : ℝ) (F₀ : α → List β) (F₁ : α → List γ) (η₀ : β → ℝ) (η₁ : γ → ℝ)
    (hε : 0 ≤ ε) (h₀ : ∀ r, 0 ≤ η₀ r) (h₁ : ∀ r, 0 ≤ η₁ r) :
    (xs.map (fun x ↦ δ + ε * (if label x then ((F₁ x).length : ℝ)
      else ((F₀ x).length : ℝ)) +
      (if label x then ((F₁ x).map η₁).sum else ((F₀ x).map η₀).sum))).sum ≤
      δ * (xs.length : ℝ) + ε * (((xs.flatMap F₀).length : ℝ) +
        ((xs.flatMap F₁).length : ℝ)) + ((xs.flatMap F₀).map η₀).sum +
        ((xs.flatMap F₁).map η₁).sum := by
  have hs {ζ : Type u} (η : ζ → ℝ) (hη : ∀ r, 0 ≤ η r) (rs : List ζ) :
      0 ≤ (rs.map η).sum := by
    induction rs with
    | nil => simp
    | cons r rs ih => simpa only [List.map_cons, List.sum_cons] using add_nonneg (hη r) ih
  have h := selected_segment_error_bound xs label δ ε (fun x ↦ (F₀ x).length)
    (fun x ↦ (F₁ x).length) (fun x ↦ ((F₀ x).map η₀).sum)
    (fun x ↦ ((F₁ x).map η₁).sum) hε
    (fun x _ ↦ hs η₀ h₀ (F₀ x))
    (fun x _ ↦ hs η₁ h₁ (F₁ x))
  have hlen {ζ : Type u} (F : α → List ζ) :
      (xs.map (fun x ↦ ((F x).length : ℝ))).sum = ((xs.flatMap F).length : ℝ) := by
    clear h
    induction xs with
    | nil => simp
    | cons x xs ih => simpa only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, Nat.cast_add] using congrArg (((F x).length : ℝ) + ·) ih
  have hsum {ζ : Type u} (F : α → List ζ) (η : ζ → ℝ) :
      (xs.map (fun x ↦ ((F x).map η).sum)).sum = ((xs.flatMap F).map η).sum := by
    clear h hlen
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append, ih]
  simpa only [hlen, hsum] using h

end SRWTightness
