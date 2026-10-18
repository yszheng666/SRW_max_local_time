import SRWTightness.RootBinomialMoment

open MeasureTheory
namespace SRWTightness

/-- Generic finite-walk strong Markov recursion and completion support.
This is an explicit foundational input, without any source scale or moment bound. -/
def FiniteRootCompletionInput : Prop :=
  ∀ D L₁ C₁ L₂ C₂ : Finset Site, L₁ ⊆ C₁ → L₂ ⊆ C₂ → C₁ ⊆ D → C₂ ⊆ D →
    Disjoint C₁ C₂ →
    (∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂) →
    ∀ x : Site,
      (∀ᵐ Y ∂killedWordMarkLaw D x,
        ∀ z ∈ wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y, z ∈ rootCompletionSet C₁ C₂) ∧
      ∀ p : ℕ, killedRootBinomialMoment D L₁ C₁ L₂ C₂ x (p + 1) =
        ∫⁻ Y, ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).map
          (fun z ↦ killedRootBinomialMoment D L₁ C₁ L₂ C₂ z p)).sum ∂killedWordMarkLaw D x

end SRWTightness
