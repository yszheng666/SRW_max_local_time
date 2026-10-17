import SRWTightness.SourceUpperActualForestError
import SRWTightness.SourceUpperBlockObservation
import SRWTightness.SourceForestMarkVisits

open Filter MeasureTheory

namespace SRWTightness

/-- Every actual block local time is the sum of its chronological forest's terminal marks. -/
theorem source_upper_block_forest_mark_visits :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ ω : Sample, domainExit (diskFinset (Real.exp t)) 0 ω ≠ ⊤ →
      ∀ y : sourceUpperBlock t b,
      (((sourceUpperBlockForest t b (wordOccupationMark (sourceUpperBlock t b)) ω).flatMap
        (finiteRecordLeaves (sourceUpperBlockForestDepth t b))).map (fun v ↦ v y)).sum =
          domainLocalTime (diskFinset (Real.exp t)) 0 y ω := by
  filter_upwards [source_upper_block_root_lt_depth, source_upper_block_observation_conditions,
    source_upper_block_domain_geometry, source_upper_block_root_coarse_range]
    with t hk ho hg hn
  intro b hb ω hfin y
  exact source_forest_mark_visits (sourceUpperRadius t)
    (upperTerminalFineRadius (sourceUpperLogRadius t))
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (sourceUpperBlockRoot t b)
    (hk b hb) b (diskFinset (Real.exp t)) (sourceUpperBlock t b) 0
    (by unfold upperTerminalFineRadius; positivity) ho.1 (ho.2 b)
    (hg _ (hn b hb) b hb).2 ω hfin y

/-- The actual block mark decomposition holds almost surely under the SRW law. -/
theorem source_upper_block_forest_mark_visits_ae :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ᵐ ω ∂pathLaw,
      ∀ y : sourceUpperBlock t b,
      (((sourceUpperBlockForest t b (wordOccupationMark (sourceUpperBlock t b)) ω).flatMap
        (finiteRecordLeaves (sourceUpperBlockForestDepth t b))).map (fun v ↦ v y)).sum =
          domainLocalTime (diskFinset (Real.exp t)) 0 y ω := by
  filter_upwards [source_upper_block_forest_mark_visits] with t ht
  intro b hb
  filter_upwards [domainExit_ne_top_ae (diskFinset (Real.exp t)) 0] with ω hfin
  exact ht b hb ω hfin

end SRWTightness
