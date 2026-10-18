import SRWTightness.GWUpperWindowIntegral
import SRWTightness.SourceUpperTerminalIntegrand
import SRWTightness.SourceUpperBranchingEndpoint

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The terminal height throughout the actual full GW band is eventually at most3t. -/
theorem source_upper_terminal_band_height (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b),
        geometricGWHeight g (sourceUpperBlockForestDepth t b) ≤ 3 * t := by
  obtain ⟨B, _, hc⟩ := source_upper_threshold_conditions hScale
  filter_upwards [source_upper_branching_depth_bounds, source_upper_barrier_terminal hScale,
    source_upper_branching_endpoint_bound hScale, hc] with t hd he hbnd ht
  intro b hb s hs hslog g hg
  have hn := sourceUpperBlockForestDepth_eq_remaining t b
  have hk := (hd b hb).1
  have hpos : 0 < sourceUpperBlockForestDepth t b := by omega
  have hsum : sourceUpperBlockRoot t b + sourceUpperBlockForestDepth t b =
      sourceUpperCoarseDepth t := by omega
  have hh := hg (sourceUpperBlockForestDepth t b) hpos le_rfl
  rw [hsum, he s] at hh
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    linarith [ht.2.2.2.2.2.2.1]
  have hp := Real.rpow_nonneg hd0 (1 / 4 : ℝ)
  have hE := hbnd s hs hslog
  unfold sourceUpperBranchingEnd at hE
  linarith

/-- The actual main terminal integral is bounded by finitely many weighted unit windows. -/
theorem source_upper_terminal_window_integral (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ (J : ℕ) (C κ : ℝ) (w : ℕ → ℝ≥0∞),
      (∀ i ∈ Finset.range (⌊2 * t + 1⌋₊ + 1),
        ∀ u ∈ Set.Ico (t - 1 + i) (t - 1 + i + 1),
          ENNReal.ofReal (sourceUpperTerminalMain t s C κ u) ≤ w i) →
      (∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b),
        sourceUpperTerminalIntegrand t s C κ (sourceUpperBlockForestDepth t b) g
        ∂geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)) ≤
      ∑ i ∈ Finset.range (⌊2 * t + 1⌋₊ + 1), w i *
        geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)
          {g | g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b)
              (sourceUpperBlockForestDepth t b) ∧
            geometricGWHeight g (sourceUpperBlockForestDepth t b) ∈
              Set.Ico (t - 1 + i) (t - 1 + i + 1)} := by
  filter_upwards [source_upper_terminal_band_height hScale] with t ht
  intro b hb s hs hslog J C κ w hw
  exact gw_upper_window_integral t J (sourceUpperBlockForestDepth t b)
    (sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b))
    (fun u ↦ ENNReal.ofReal (sourceUpperTerminalMain t s C κ u)) w (ht b hb s hs hslog) hw

end SRWTightness
