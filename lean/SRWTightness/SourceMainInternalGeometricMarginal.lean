import SRWTightness.SourceMainInternalOrderedMixtures
import SRWTightness.GeometricGWOneRootMarginalInternal

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with the actual closed geometric marginal internally proved;
all other remaining interfaces retain their original explicit scopes. -/
theorem source_main_claims_internal_geometric_marginal [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)]
    (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput)
    (hExt : ExteriorBridgeFactorizationInput)
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


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput)
    (hTranslation : ProjectedMarkTranslationInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_ordered_mixtures hLast hrec
    geometric_gw_one_root_marginal_input_internal hExt hErase hR hP hH hM hT hExit hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit Cm hMoment
    hIncrement hLower hSum hBound hKernel hEndpoint hOcc hRes hBDZ hSup hGreen hEmbed hTranslation

end SRWTightness
