import SRWTightness.SourceEarlyPairEndpointBound
import SRWTightness.SourceCenteredSuccessEvent

open MeasureTheory Filter
namespace SRWTightness

/-- The early pair estimate holds for one common fine level and its canonical center events. -/
theorem source_early_centered_pair_endpoint_bound [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
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
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) :
    ∃ A C : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      3 ≤ J₀ ∧ 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let q := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
      ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      sourceEnlargedLaw.real
        (sourceCenteredSuccessEvent t A (2 / 5) b I ∩ sourceCenteredSuccessEvent t A (2 / 5) w I) ≤
      C * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 / (Real.exp t) ^ 4 *
        Real.exp (-4 * ν - q ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * q + C * ((J : ℝ) + 1)) := by
  obtain ⟨A, C, J₀, a₀, hA, hC, hJ₀, ha₀, hp⟩ :=
    source_early_pair_endpoint_bound hLast hrec hMarginal hJoint hExt hFlat hErase hR hP
      hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive
      hInitial hHit Cm hMoment hIncrement
  refine ⟨A, C, J₀, a₀, hA, hC, hJ₀, ha₀, ?_⟩
  filter_upwards [hp] with t hp
  intro b w hb hw hbw ha hrange
  dsimp only
  intro I hI
  obtain ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, hpair⟩ := hp b w hb hw hbw ha hrange
  have h0 := source_observation_level_unique t A I₀ I hI₀ hI
  have h1 := source_observation_level_unique t A I₁ I hI₁ hI
  subst I₀
  subst I₁
  intro cm cs clm cls lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
  rw [source_centered_success_event_eq t A (2 / 5) b I z₀ hz₀,
    source_centered_success_event_eq t A (2 / 5) w I z₁ hz₁]
  exact hpair hGW₀ hGW₁ hMix

end SRWTightness
