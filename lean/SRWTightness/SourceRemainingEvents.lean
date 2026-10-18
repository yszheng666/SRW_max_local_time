import SRWTightness.SourceSiteFineSuccess
import SRWTightness.SourceConditionalActualForests

open MeasureTheory Filter
namespace SRWTightness

/-- Remaining success uses the original fine forest, root count, and auxiliary bridges. -/
def sourceSiteRemainingSuccessEvent (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ν : ℕ) :
    Set (Sample × (Site → ℕ → GaussianCoefficientSpace)) :=
  {p | (sourceActualFineForest t b
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν p.1, p.2 b) ∈
    sourceContinuationForestEvent t A γ b I z ν
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
      (sourceActualCount t b ν p.1)}

/-- The corresponding two-site remaining event on fixed labeled records and selected auxiliaries. -/
def sourceTaggedRemainingEvent (t A γ : ℝ) (b w : Site) (I₀ I₁ ν : ℕ)
    (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
    (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))
    (h : ExteriorPathRecord) (k l : ℕ) :
    Set ((Fin h.1.length → SourceExteriorFineValue t
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
      (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν) ×
        ((ℕ → GaussianCoefficientSpace) × (ℕ → GaussianCoefficientSpace))) :=
  {q | ((orderedTaggedForests q.1).1, q.2.1) ∈
      sourceContinuationForestEvent t A γ b I₀ z₀ ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) k ∧
    ((orderedTaggedForests q.1).2, q.2.2) ∈
      sourceContinuationForestEvent t A γ w I₁ z₁ ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) l}

/-- Original complete success implies the explicitly named remaining event almost surely. -/
theorem source_site_remaining_success_inclusion (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      0 ≤ γ → 1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      b ∈ sourceCandidateAnnulus (Real.exp t) → ∀ ν : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ∀ᵐ p ∂sourceEnlargedLaw,
      p ∈ sourceSiteSuccessEvent t A γ b I z →
      p ∈ sourceSiteRemainingSuccessEvent t A γ b I z ν := by
  exact source_site_fine_success_inclusion hF

end SRWTightness
