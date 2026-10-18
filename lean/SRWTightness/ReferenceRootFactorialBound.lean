import SRWTightness.ReferenceWordLIntegral
import SRWTightness.RootFactorialFirstMean

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- At positive orders the empty reference mark contributes zero. -/
theorem reference_root_binomial_mixture (D K L₁ C₁ L₂ C₂ : Finset Site)
    (α : ℝ) (p : ℕ) :
    rootBinomialMoment (referenceWordMarkLaw D K α) L₁ C₁ L₂ C₂ (p + 1) =
      ∑ x ∈ K, ENNReal.ofReal (α * equilibriumMeasure D K x) *
        killedRootBinomialMoment D L₁ C₁ L₂ C₂ x (p + 1) := by
  simp only [rootBinomialMoment, killedRootBinomialMoment, lintegral_referenceWordMark]
  simp [wordMarkRootCount]

/-- A componentwise initial-mean factor survives the exact reference mixture. -/
theorem reference_root_factorial_from_components (D K L₁ C₁ L₂ C₂ : Finset Site)
    (α : ℝ) (R : ℝ≥0∞) (p : ℕ)
    (hb : ∀ x ∈ K, killedRootBinomialMoment D L₁ C₁ L₂ C₂ x (p + 1) ≤
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 * R ^ p) :
    rootBinomialMoment (referenceWordMarkLaw D K α) L₁ C₁ L₂ C₂ (p + 1) ≤
      rootBinomialMoment (referenceWordMarkLaw D K α) L₁ C₁ L₂ C₂ 1 * R ^ p := by
  rw [reference_root_binomial_mixture]
  rw [show (1 : ℕ) = 0 + 1 by rfl, reference_root_binomial_mixture]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x hx
  simpa only [mul_assoc] using
    mul_le_mul_left' (hb x hx) (ENNReal.ofReal (α * equilibriumMeasure D K x))

/-- The generic completion input yields the reference-mark factorial estimate. -/
theorem reference_root_factorial_bound (hrec : FiniteRootCompletionInput)
    (D K L₁ C₁ L₂ C₂ : Finset Site) (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hC₁ : C₁ ⊆ D) (hC₂ : C₂ ⊆ D) (hdis : Disjoint C₁ C₂)
    (hexit : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (α : ℝ) (R : ℝ≥0∞)
    (hmean : ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 ≤ R) (p : ℕ) :
    rootBinomialMoment (referenceWordMarkLaw D K α) L₁ C₁ L₂ C₂ (p + 1) ≤
      rootBinomialMoment (referenceWordMarkLaw D K α) L₁ C₁ L₂ C₂ 1 * R ^ p := by
  apply reference_root_factorial_from_components
  intro x hx
  exact killed_root_factorial_first_mean hrec D L₁ C₁ L₂ C₂ hL₁ hL₂ hC₁ hC₂
    hdis hexit R hmean p x

end SRWTightness
