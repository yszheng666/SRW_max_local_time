import SRWTightness.SourceUpperTerminalWindows

open Filter

namespace SRWTightness

/-- Actual terminal-window support gives the manuscript deficit cutoff, before barrier enlargement. -/
theorem source_upper_terminal_window_deficit (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, ∀ g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b)
        (sourceUpperBlockForestDepth t b), ∀ u : ℝ,
      u ≤ geometricGWHeight g (sourceUpperBlockForestDepth t b) →
      -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
        sourceUpperTarget t s - u := by
  filter_upwards [source_upper_branching_depth_bounds, source_upper_barrier_terminal hScale]
    with t hd he
  intro b hb s g hg u hu
  have hn := sourceUpperBlockForestDepth_eq_remaining t b
  have hk := (hd b hb).1
  have hpos : 0 < sourceUpperBlockForestDepth t b := by omega
  have hsum : sourceUpperBlockRoot t b + sourceUpperBlockForestDepth t b =
      sourceUpperCoarseDepth t := by omega
  have hh := hg (sourceUpperBlockForestDepth t b) hpos le_rfl
  rw [hsum, he s] at hh
  linarith

end SRWTightness
