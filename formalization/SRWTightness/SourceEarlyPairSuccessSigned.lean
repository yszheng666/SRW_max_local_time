import SRWTightness.SourceEarlyPairSuccessBound
import SRWTightness.SourceLiteralDistanceRanges

open MeasureTheory Filter

namespace SRWTightness

/-- The actual early pair success estimate using the literal signed manuscript distance index. -/
theorem source_early_pair_success_signed (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) (hErase : ExteriorNestedCountInvarianceInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) (hExit : FiniteKilledWalkMomentInput)
    (hGW : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A C : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      3 ≤ J₀ ∧ 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → (a₀ : ℤ) ≤ sourceSignedDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceSignedDistanceIndex t (Real.sqrt (normSq (w - b))) <
        ((sourceCoarseLowerLevel t + sourceCommonPairGap t : ℕ) : ℤ) →
      let a := (sourceSignedDistanceIndex t (Real.sqrt (normSq (w - b)))).toNat
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      ∃ I₀ I₁ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) ∧
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₁) ∧
      ∃ (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      (z₀ : Site) = b ∧ (z₁ : Site) = w ∧ ∀
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)),
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I₀ z₀ ∩ sourceSiteSuccessEvent t A γ w I₁ z₁) ≤
      C * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
        ∫ ω, (sourceEarlyPrefixEvent t b j).indicator (fun u ↦ Real.exp
          (2 * Real.sqrt (2 * (sourceActualCount t b ν u : ℝ)) +
            2 * Real.sqrt (2 * (sourceActualCount t w ν u : ℝ)))) ω ∂pathLaw := by
  obtain ⟨A, C, J₀, a₀, hA, hC, hJ₀, ha₀, hh⟩ := source_early_pair_success_bound
    hExt hFlat hErase hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, C, J₀, a₀, hA, hC, hJ₀, ha₀, ?_⟩
  filter_upwards [hh] with t ht
  intro b w hb hw hbw ha hrange
  have hn := (source_signed_early_range_iff t (Real.sqrt (normSq (w - b))) a₀
    (sourceCoarseLowerLevel t + sourceCommonPairGap t) (by omega)).mp ⟨ha, hrange⟩
  dsimp only
  rw [source_signed_distance_toNat]
  exact ht b w hb hw hbw hn.1 hn.2

end SRWTightness
