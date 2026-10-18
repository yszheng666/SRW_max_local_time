import SRWTightness.ReferenceWordRootMean

open MeasureTheory
namespace SRWTightness

/-- Both label counts are evaluated on the same ordered mark. -/
theorem referenceWordMark_pair_mean (hLast : FiniteLastVisitCountInput)
    (D K L₁ C₁ L₂ C₂ : Finset Site) (hKD : K ⊆ D)
    (hL₁K : L₁ ⊆ K) (hL₂K : L₂ ⊆ K) (hL₁C : L₁ ⊆ C₁) (hL₂C : L₂ ⊆ C₂)
    (hC₁D : C₁ ⊆ D) (hC₂D : C₂ ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) :
    (∫ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)
      ∂referenceWordMarkLaw D K α) = α * (capacity C₁ L₁ + capacity C₂ L₂) := by
  simp only [Nat.cast_add]
  rw [integral_add
    (integrable_referenceWordMark_roots hLast D K L₁ C₁ hL₁C hC₁D α)
    (integrable_referenceWordMark_roots hLast D K L₂ C₂ hL₂C hC₂D α),
    referenceWordMark_root_mean hLast D K L₁ C₁ hKD hL₁K hL₁C hC₁D α hα hcap,
    referenceWordMark_root_mean hLast D K L₂ C₂ hKD hL₂K hL₂C hC₂D α hα hcap]
  ring

end SRWTightness
