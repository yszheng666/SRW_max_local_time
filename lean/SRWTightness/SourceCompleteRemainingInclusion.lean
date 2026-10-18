import SRWTightness.SourceRemainingEvents
import SRWTightness.SourceSuccessPrefix
import SRWTightness.SourceContinuationRange

open MeasureTheory Filter
namespace SRWTightness

/-- Complete two-site success supplies both remaining events, the original prefix and both
original root caps. The inclusion is on the single common enlarged probability space. -/
theorem source_complete_remaining_inclusion (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (b w : Site) (I₀ I₁ j ν : ℕ)
      (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
      (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      0 ≤ γ → 1 ≤ A * diskEnergyGapRatio ^ I₀ →
      A * diskEnergyGapRatio ^ I₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ A * diskEnergyGapRatio ^ I₁ →
      A * diskEnergyGapRatio ^ I₁ ≤ sourceLowerRadius t / t ^ 6 →
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      j ≤ ν → ν ≤ 2 * sourceCoarseLowerLevel t → ∀ᵐ p ∂sourceEnlargedLaw,
      p ∈ sourceSiteSuccessEvent t A γ b I₀ z₀ ∩ sourceSiteSuccessEvent t A γ w I₁ z₁ →
      p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
      p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
      p.1 ∈ sourceEarlyPrefixEvent t b j ∧
      sourceActualCount t b ν p.1 ≤ sourceEarlyRootCap t ν ∧
      sourceActualCount t w ν p.1 ≤ sourceEarlyRootCap t ν := by
  filter_upwards [source_site_remaining_success_inclusion hF,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    source_continuation_cutoff_reserve, source_deficit_large_conditions,
    eventually_ge_atTop (0 : ℝ)] with t hinc hN htime hreserve hlarge ht
  intro A γ b w I₀ I₁ j ν z₀ z₁ hγ ha₀ hc₀ ha₁ hc₁ hb hw hj hν
  have hνreal : (ν : ℝ) ≤
      ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hνdepth : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by
    exact_mod_cast hνreal
  have hνcast : (ν : ℝ) ≤ 2 * (sourceCoarseLowerLevel t : ℝ) := by
    exact_mod_cast hν
  have hntime : 0 ≤ (sourceCoarseGeneration t : ℝ) := by
    rw [← hN.2]
    positivity
  have hνtime : (ν : ℝ) ≤ sourceTotalTime t := by
    unfold sourceTotalTime
    linarith
  have hθ := (sourceBarrierSlope_bounds t hlarge.1 hlarge.2.1).1
  filter_upwards [hinc A γ b I₀ z₀ hγ ha₀ hc₀ hb ν hν,
    hinc A γ w I₁ z₁ hγ ha₁ hc₁ hw ν hν] with p hp₀ hp₁
  intro hp
  exact ⟨hp₀ hp.1, hp₁ hp.2,
    source_site_success_prefix t A γ b I₀ j z₀ (hj.trans hνdepth) p hp.1,
    source_site_success_count_cap t A γ b I₀ ν z₀ hνdepth hθ hνtime p hp.1,
    source_site_success_count_cap t A γ w I₁ ν z₁ hνdepth hθ hνtime p hp.2⟩

end SRWTightness
