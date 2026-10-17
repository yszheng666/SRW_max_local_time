import SRWTightness.SourceUpperTerminalWindowWeight
import SRWTightness.SourceUpperBranchingWindowBound

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The branching upper bound at the actual remaining forest depth. -/
noncomputable def sourceUpperBranchingWindowFactor (t s C : ℝ) (k J : ℕ) (u : ℝ) : ℝ :=
  let L := sourceUpperCoarseDepth t - k
  C * (5 + s + k) * sourceUpperBranchingSlack t s u / (L : ℝ) ^ 2 *
    (J : ℝ) ^ (1 / 4 : ℝ) *
      Real.exp (-u ^ 2 / (2 * L) + (u / L) * Real.sqrt (2 * (J : ℝ)))

/-- The full GW band enforces the terminal branching endpoint. -/
theorem source_upper_terminal_band_endpoint (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b),
        geometricGWHeight g (sourceUpperBlockForestDepth t b) ≤ sourceUpperBranchingEnd t s := by
  obtain ⟨B, _, hc⟩ := source_upper_threshold_conditions hScale
  filter_upwards [source_upper_branching_depth_bounds, source_upper_barrier_terminal hScale, hc]
    with t hd he ht
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
  unfold sourceUpperBranchingEnd
  linarith

/-- Actual band-window probabilities obey the branching bound and vanish past its endpoint. -/
theorem source_upper_terminal_window_probability (hScale : ExponentialFloorScaleInput)
    (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ, 0 < J → (J : ℝ) ≤ t ^ 2 →
      ∀ u : ℝ, t - 1 ≤ u →
      geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)
        {g | g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b)
            (sourceUpperBlockForestDepth t b) ∧
          geometricGWHeight g (sourceUpperBlockForestDepth t b) ∈ Set.Ico u (u + 1)} ≤
        if u ≤ sourceUpperBranchingEnd t s then
          ENNReal.ofReal (sourceUpperBranchingWindowFactor t s C (sourceUpperBlockRoot t b) J u)
        else 0 := by
  obtain ⟨C, hC, hp⟩ := source_upper_branching_window_bound hScale hGW
  refine ⟨C, hC, ?_⟩
  filter_upwards [hp, source_upper_terminal_band_endpoint hScale] with t ht he
  intro b hb s hs hslog J hJ hJcap u hu
  by_cases hue : u ≤ sourceUpperBranchingEnd t s
  · rw [if_pos hue]
    have hn := sourceUpperBlockForestDepth_eq_remaining t b
    have hsub :
        {g : GeometricGWRecord |
          g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b) ∧
          geometricGWHeight g (sourceUpperBlockForestDepth t b) ∈ Set.Ico u (u + 1)} ⊆
        {g | (∀ j : ℕ, 0 < j → j < sourceUpperCoarseDepth t - sourceUpperBlockRoot t b →
          geometricGWHeight g j ≤ sourceUpperBarrier t s (sourceUpperBlockRoot t b + j)) ∧
          geometricGWHeight g (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b) ∈
            Set.Ico u (u + 1)} := by
      intro g hg
      refine ⟨fun j hj hjn ↦ hg.1 j hj (by omega), ?_⟩
      simpa only [hn] using hg.2
    have hm := measureReal_mono hsub
      (measure_ne_top (geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)) _)
    have hbound := ht b hb s hs hslog J hJ hJcap u hu hue
    rw [hn] at hm ⊢
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (hm.trans hbound)
  · rw [if_neg hue]
    have hempty :
        {g : GeometricGWRecord |
          g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b) ∧
          geometricGWHeight g (sourceUpperBlockForestDepth t b) ∈ Set.Ico u (u + 1)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro g hg
      exact hue (hg.2.1.trans (he b hb s hs hslog g hg.1))
    rw [hempty, measure_empty]

end SRWTightness
