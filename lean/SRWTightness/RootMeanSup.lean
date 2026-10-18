import SRWTightness.RootBinomialMoment

open scoped ENNReal
namespace SRWTightness

/-- The actual supremum of first future-root means over all completion states. -/
noncomputable def killedRootMeanSup (D L₁ C₁ L₂ C₂ : Finset Site) : ℝ≥0∞ :=
  ⨆ x : rootCompletionSet C₁ C₂, killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1

theorem killedRootMean_le_sup (D L₁ C₁ L₂ C₂ : Finset Site) (x : Site)
    (hx : x ∈ rootCompletionSet C₁ C₂) :
    killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 ≤ killedRootMeanSup D L₁ C₁ L₂ C₂ :=
  le_iSup (fun z : rootCompletionSet C₁ C₂ ↦
    killedRootBinomialMoment D L₁ C₁ L₂ C₂ z 1) ⟨x, hx⟩

theorem killedRootMeanSup_le (D L₁ C₁ L₂ C₂ : Finset Site) (R : ℝ≥0∞)
    (hR : ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 ≤ R) :
    killedRootMeanSup D L₁ C₁ L₂ C₂ ≤ R :=
  iSup_le (fun x ↦ hR x x.property)

end SRWTightness
