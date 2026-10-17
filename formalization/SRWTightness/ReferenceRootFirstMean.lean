import SRWTightness.RootFirstMomentReal
import SRWTightness.ReferenceWordRootMean

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- The reference first factorial moment is the actual integrable real total-root mean. -/
theorem reference_root_first_mean_ofReal (hLast : FiniteLastVisitCountInput)
    (D K L₁ C₁ L₂ C₂ : Finset Site) (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hC₁ : C₁ ⊆ D) (hC₂ : C₂ ⊆ D) (α : ℝ) :
    rootBinomialMoment (referenceWordMarkLaw D K α) L₁ C₁ L₂ C₂ 1 = ENNReal.ofReal
      (∫ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)
        ∂referenceWordMarkLaw D K α) := by
  apply rootBinomialMoment_one_ofReal
  have h₁ := integrable_referenceWordMark_roots hLast D K L₁ C₁ hL₁ hC₁ α
  have h₂ := integrable_referenceWordMark_roots hLast D K L₂ C₂ hL₂ hC₂ α
  convert h₁.add h₂ using 1
  · rfl
  · funext Y
    exact Nat.cast_add _ _

end SRWTightness
