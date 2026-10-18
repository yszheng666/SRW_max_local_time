import SRWTightness.SourceUpperBranchingEndpoint
import SRWTightness.SourceUpperBranchingProbability

open Filter MeasureTheory

namespace SRWTightness

/-- Actual block parameters satisfy the branching estimate throughout its window range. -/
theorem source_upper_actual_branching_probability (hScale : ExponentialFloorScaleInput)
    (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ J : ℕ, 0 < J → (J : ℝ) ≤ t ^ 2 →
      ∀ u : ℝ, t - 1 ≤ u → u ≤ sourceUpperBranchingEnd t s →
      let k := sourceUpperBlockRoot t b
      let L := sourceUpperCoarseDepth t - k
      let x := Real.sqrt (2 * (J : ℝ))
      (geometricGWRecordLaw J L).real
        {r | (∀ j : ℕ, 0 < j → j < L →
          geometricGWHeight r j ≤ sourceUpperBarrier t s (k + j)) ∧
          geometricGWHeight r L ∈ Set.Ico u (u + 1)} ≤
        C * gwBarrierPrefactor L x u (sourceUpperBranchingStart t s k x)
          (sourceUpperBranchingEnd t s) * Real.sqrt (x / (u * L)) := by
  obtain ⟨C, hC, hh⟩ := source_upper_branching_probability hGW
  obtain ⟨B, _, hc⟩ := source_upper_threshold_conditions hScale
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_upper_branching_endpoint_bound hScale,
    source_upper_branching_depth_bounds, source_upper_branching_initial_range, hc,
    eventually_ge_atTop (3 : ℝ)] with t he hd hi ht ht3
  intro b hb s hs hslog J hJ hJcap u hu hub
  dsimp only
  have hT : 0 < sourceUpperTotalDepth t := by linarith [ht.2.2.2.1]
  have hy := (source_upper_height_bounds t s ht.1 hs hslog).1
  have hθ : 0 ≤ sourceUpperSlope t s := div_nonneg (by linarith) hT.le
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) := by
    linarith [ht.2.2.2.2.2.2.1]
  have hu2 : Real.sqrt 2 ≤ u := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have huL : u ≤ 4 * (sourceUpperCoarseDepth t - sourceUpperBlockRoot t b : ℕ) := by
    linarith [(hd b hb).2.1, he s hs hslog]
  exact hh t s u (sourceUpperBlockRoot t b) J (hd b hb).1 hJ hs hθ hd0
    (hi b hb J hJcap) hu2 huL hub

end SRWTightness
