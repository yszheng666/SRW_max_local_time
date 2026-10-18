import SRWTightness.CompletionMomentBound

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- The initial mean factor is retained for a walk started at any site. -/
theorem killed_root_factorial_first_mean (hrec : FiniteRootCompletionInput)
    (D L₁ C₁ L₂ C₂ : Finset Site) (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hC₁ : C₁ ⊆ D) (hC₂ : C₂ ⊆ D) (hdis : Disjoint C₁ C₂)
    (hexit : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (R : ℝ≥0∞)
    (hmean : ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 ≤ R) :
    ∀ p : ℕ, ∀ x : Site, killedRootBinomialMoment D L₁ C₁ L₂ C₂ x (p + 1) ≤
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 * R ^ p := by
  intro p x
  obtain ⟨hs, heq⟩ := hrec D L₁ C₁ L₂ C₂ hL₁ hL₂ hC₁ hC₂ hdis hexit x
  rw [heq p]
  exact completion_moment_sum_bound _ _ _ _ _ _ _ _ hs
    (killed_root_factorial_bound hrec D L₁ C₁ L₂ C₂ hL₁ hL₂ hC₁ hC₂ hdis hexit R hmean p)

/-- Finite uniform mean bounds prove finiteness of all factorial moments at exits. -/
theorem killed_root_factorial_finite (hrec : FiniteRootCompletionInput)
    (D L₁ C₁ L₂ C₂ : Finset Site) (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hC₁ : C₁ ⊆ D) (hC₂ : C₂ ⊆ D) (hdis : Disjoint C₁ C₂)
    (hexit : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (R : ℝ≥0∞)
    (hmean : ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 ≤ R) (hR : R < ∞) :
    ∀ p : ℕ, ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x p < ∞ := by
  intro p x hx
  exact (killed_root_factorial_bound hrec D L₁ C₁ L₂ C₂ hL₁ hL₂ hC₁ hC₂
    hdis hexit R hmean p x hx).trans_lt (ENNReal.pow_lt_top hR)

end SRWTightness
