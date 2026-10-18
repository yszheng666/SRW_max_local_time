import SRWTightness.SourceUpperBlockVisits
import SRWTightness.SourceForwardDirectCount

open Filter MeasureTheory

namespace SRWTightness

/-- Actual forward forest counts equal directly extracted buffered traversals almost surely. -/
theorem source_upper_block_count_eq_direct_ae (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ᵐ ω ∂pathLaw,
      ∀ j : ℕ, sourceUpperBlockRoot t b ≤ j → j ≤ sourceUpperCoarseDepth t →
      sourceUpperBlockCount t b j ω =
        (killedChildIntervals (diskFinset (Real.exp t)) (sourceUpperBlockInner t j b)
          (sourceUpperBlockOuter t j b) 0 ω).length := by
  filter_upwards [source_upper_block_observation_conditions,
    source_upper_block_domain_geometry, source_upper_block_root_coarse_range,
    source_upper_block_root_lt_depth] with t ho hg hn hk
  intro b hb
  filter_upwards [domainExit_ne_top_ae (diskFinset (Real.exp t)) 0] with ω hfin
  intro j hj hJ
  exact source_forward_count_eq_direct hF (sourceUpperRadius t)
    (upperTerminalFineRadius (sourceUpperLogRadius t))
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) (sourceUpperBlockRoot t b) j
    (by unfold upperTerminalFineRadius; positivity) ho.1 hj (by
      have := hk b hb
      change j ≤ sourceRootDepth (Real.exp t) (sourceUpperRadius t) - 1 at hJ
      omega) b (diskFinset (Real.exp t)) (hg _ (hn b hb) b hb).2 0 ω hfin

end SRWTightness
