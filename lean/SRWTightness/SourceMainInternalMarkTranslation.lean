import SRWTightness.SourceMainInternalStretchedExponential
import SRWTightness.ProjectedMarkTranslationInternal

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with projected reference-mark translation internally proved;
all other remaining interfaces retain their original explicit scopes. -/
theorem source_main_claims_internal_mark_translation [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)]
    (hExt : ExteriorBridgeFactorizationInput)
    (hErase : ExteriorNestedCountInvarianceInput)
    (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput)
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
    (hKernel : FiniteGaussianBridgeKernelInput) (hEndpoint : GaussianEndpointResidualInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_stretched_exponential
    hExt hErase hP hH hGW hReconstruct hBE
    hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm hMoment hIncrement hLower hKernel hEndpoint
    hBDZ hSup hGreen hEmbed projected_mark_translation_input_internal

end SRWTightness
