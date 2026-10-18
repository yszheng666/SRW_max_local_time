import SRWTightness.RootBinomialMoment
import SRWTightness.KilledWordPairMean

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- The nonnegative first moment equals the established real mean when the count is integrable. -/
theorem rootBinomialMoment_one_ofReal (μ : Measure WordMark) (L₁ C₁ L₂ C₂ : Finset Site)
    (hi : Integrable (fun Y ↦
      ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)) μ) :
    rootBinomialMoment μ L₁ C₁ L₂ C₂ 1 = ENNReal.ofReal
      (∫ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ) ∂μ) := by
  rw [rootBinomialMoment_one, ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun Y ↦ Nat.cast_nonneg _))]
  simp only [ENNReal.ofReal_natCast]

/-- Generic last-visit integrability connects the killed-walk first moments exactly. -/
theorem killedRootBinomialMoment_one_ofReal (hLast : FiniteLastVisitCountInput)
    (D L₁ C₁ L₂ C₂ : Finset Site) (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hC₁ : C₁ ⊆ D) (hC₂ : C₂ ⊆ D) (x : Site) :
    killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 = ENNReal.ofReal
      (∫ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)
        ∂killedWordMarkLaw D x) := by
  apply rootBinomialMoment_one_ofReal
  have h₁ := integrable_killedWordMark_roots hLast D L₁ C₁ hL₁ hC₁ x
  have h₂ := integrable_killedWordMark_roots hLast D L₂ C₂ hL₂ hC₂ x
  convert h₁.add h₂ using 1
  · rfl
  · funext Y
    exact Nat.cast_add _ _

end SRWTightness
