import SRWTightness.GaussianRegressionInternal
import SRWTightness.WordFlatteningInternal
import SRWTightness.ExponentialFloorScaleProof
import SRWTightness.SourceDiskUpperTail
import SRWTightness.SourceDiskSeed
import SRWTightness.MainConditionalReduction

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints from the constructed spatial estimates, with internally
proved finite-word flattening, floor scales and Gaussian regression. The remaining external
    interfaces stay explicit. -/
theorem source_main_claims_internal_flattening_and_scale_regression_internal [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
    (hErase : ExteriorNestedCountInvarianceInput)
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

    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hPositiveSum : PositiveConvolutionInput) (hPositiveMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput)
    (hTranslation : ProjectedMarkTranslationInput)
    (hTree : ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      MarkedGWTreeInput (Mark (sourceUpperBlock t b))) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  have hu := source_disk_upper_tail_claim two_level_word_flattening_input_internal hP
    finite_gaussian_regression_input_internal hBDZ hSup
    hPositiveSum
    hPositiveMoment hConv hMills hIntegral hGreen hEmbed exponential_floor_scale_input hDisk
    hTranslation hGW hTree
    (Eventually.of_forall (fun t b _ ↦ hAllForest (sourceUpperBlock t b)))
  have hs := source_disk_seed_claim hDisk hAnnulus hLast hrec hMarginal
    hJoint hExt two_level_word_flattening_input_internal hErase hR hP hH hM hT hExit hGW
    hReconstruct hBE hGaussian hReflection
    hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement hLower hSum hBound hKernel
    hEndpoint hOcc hRes hAllForest hAllMix
  exact mainClaims_of_spatial_inputs hu hs

end SRWTightness
