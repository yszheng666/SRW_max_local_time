import SRWTightness.SourceFineSuccessInclusion
import SRWTightness.SourceSiteBridgeLaw

open MeasureTheory Filter
namespace SRWTightness

/-- The actual continuation-forest inclusion holds on the common space carrying both sites' bridges. -/
theorem source_site_fine_success_inclusion (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b : Site) (I : ℕ)
      (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      0 ≤ γ → 1 ≤ A * diskEnergyGapRatio ^ I →
      A * diskEnergyGapRatio ^ I ≤ sourceLowerRadius t / t ^ 6 →
      b ∈ sourceCandidateAnnulus (Real.exp t) → ∀ ν : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ∀ᵐ p ∂sourceEnlargedLaw,
      p ∈ sourceSiteSuccessEvent t A γ b I z →
      (sourceActualFineForest t b (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν p.1,
        p.2 b) ∈ sourceContinuationForestEvent t A γ b I z ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        (sourceActualCount t b ν p.1) := by
  filter_upwards [source_fine_success_inclusion hF] with t ht
  intro A γ b I z hγ ha hc hb ν hν
  exact (source_site_projection_preserving b).quasiMeasurePreserving.ae
    (ht A γ b I z hγ ha hc hb ν hν)

end SRWTightness
