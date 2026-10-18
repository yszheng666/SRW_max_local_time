import SRWTightness.SourceContinuationRadiusBound
import SRWTightness.SourceContinuationNonnegative
import SRWTightness.SourceRootCapHeight
import SRWTightness.ContinuationPairProduct

open Filter MeasureTheory
namespace SRWTightness

/-- The two actual source continuation probabilities have the joint exponential envelope used
in equation 8.11, uniformly for the original capped root counts. -/
theorem source_continuation_pair_radius_upper_bound (hGW : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, ∃ I₀ I₁ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) ∧
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₁) ∧
      ∃ (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      (z₀ : Site) = b ∧ (z₁ : Site) = w ∧
      ∀ ν k l : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      sourceContinuationProbability t A γ b I₀ z₀ ν k *
        sourceContinuationProbability t A γ w I₁ z₁ ν l ≤
      C * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
        Real.exp (2 * Real.sqrt (2 * (k : ℝ)) + 2 * Real.sqrt (2 * (l : ℝ))) := by
  obtain ⟨A, C, hA, hC, ht⟩ := source_continuation_radius_upper_bound hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, C ^ 2, hA, pow_pos hC 2, ?_⟩
  filter_upwards [ht, source_deficit_large_conditions] with t ht hlarge
  intro b w
  obtain ⟨I₀, hI₀, z₀, hz₀, hb⟩ := ht b
  obtain ⟨I₁, hI₁, z₁, hz₁, hw⟩ := ht w
  refine ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, ?_⟩
  intro ν k l hν hk hl
  have hθ := (sourceBarrierSlope_bounds t hlarge.1 hlarge.2.1).1
  exact continuation_pair_product_bound C (ν : ℝ) t _ _ _ _ hC.le (Nat.cast_nonneg _)
    (source_continuation_probability_nonneg t A γ w I₁ z₁ ν l)
    (hb ν k hν (source_early_root_height_of_cap t ν k hθ hk))
    (hw ν l hν (source_early_root_height_of_cap t ν l hθ hl))

end SRWTightness
