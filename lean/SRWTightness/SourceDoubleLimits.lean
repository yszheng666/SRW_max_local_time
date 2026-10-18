import SRWTightness.SourceMainClaims
import SRWTightness.TightnessDoubleLimits

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- The literal disk and time double limits, including the inclusive endpoint convention. -/
theorem source_double_limits [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hLast : FiniteLastVisitCountInput)
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
    (hIncrement : BesselThreeIncrementInput)
    (hLower : GWBarrierLowerInput)
    (hSum : SeparatedStretchedExponentialSumInput)
    (hBound : QuadraticStretchedExponentialBoundInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hEndpoint : GaussianEndpointResidualInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (hAllForest : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWForestJointInput (Mark K))
    (hAllMix : ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
      [MeasurableSpace (List α)] [MeasurableSpace (List β)]
      [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)],
      OrderedForestMixtureInput α β)
    (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hPositiveSum : PositiveConvolutionInput) (hPositiveMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hTranslation : ProjectedMarkTranslationInput)
    (hTree : ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      MarkedGWTreeInput (Mark (sourceUpperBlock t b))) :
    Tendsto (fun K : ℝ ↦ limsup
      (fun R : ℝ ↦ pathLaw.real {ω | K < |diskFluctuation R ω|}) atTop)
      atTop (𝓝 0) ∧
    Tendsto (fun K : ℝ ↦ limsup
      (fun n : ℕ ↦ pathLaw.real {ω | K < |timeFluctuation n ω|}) atTop)
      atTop (𝓝 0) ∧
    Tendsto (fun K : ℝ ↦ limsup
      (fun n : ℕ ↦ pathLaw.real
        {ω | K < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n|}) atTop)
      atTop (𝓝 0) := by
  obtain ⟨hd, _, ht, _, hi⟩ := source_main_claims hDisk hAnnulus hLast hrec hMarginal
    hJoint hExt hFlat hErase hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection
    hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement hLower hSum hBound hKernel
    hEndpoint hOcc hRes hAllForest hAllMix hReg hBDZ hSup hPositiveSum hPositiveMoment
    hConv hMills hIntegral hGreen hEmbed hScale hTranslation hTree
  exact ⟨disk_tightness_double_limit hd, time_tightness_double_limit ht,
    inclusive_time_tightness_double_limit hi⟩

end SRWTightness
