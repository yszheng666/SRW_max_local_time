import SRWTightness.SourceForestContinuationCoordinates
import SRWTightness.SourceWalkSuccessEvent

open MeasureTheory
namespace SRWTightness

/-- The original full coarse event implies the shifted continuation band of the actual fine forest. -/
theorem source_fine_continuation_band (hF : TwoLevelWordFlatteningInput)
    (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (hm : 16 ≤ sourceLowerRadius t)
    (hν : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (hD : sourceExitDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b 0 ⊆ diskFinset (Real.exp t)) :
    ∀ᵐ ω ∂pathLaw, sourceWalkCoarseBand t b ω →
      forestPopulationList (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        (sourceActualFineForest t b K ν ω) ∈
      sourceContinuationBand t ν (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) := by
  filter_upwards [source_fine_continuation_population hF t b K ν hm hν hD] with ω hp
  intro hbar
  constructor
  · intro i hi hin
    unfold geometricGWHeight
    rw [hp i hin]
    exact hbar.1 (ν + i) (by omega) (by omega)
  · unfold geometricGWHeight
    rw [hp _ le_rfl]
    have he : ν + (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) =
        sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by omega
    rw [he]
    exact hbar.2

end SRWTightness
