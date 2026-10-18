import SRWTightness.SourceMainInternalMarkTranslation
import SRWTightness.GaussianEndpointResidualInternal

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with Gaussian endpoint-residual reconstruction
proved internally;
all other remaining interfaces retain their original explicit scopes. -/
theorem source_main_claims_internal_gaussian_endpoint [MeasurableSpace (List
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
    (hKernel : FiniteGaussianBridgeKernelInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_mark_translation
    hExt hErase hP hH hGW hReconstruct hBE
    hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm hMoment hIncrement hLower hKernel
    gaussian_endpoint_residual_input_internal
    hBDZ hSup hGreen hEmbed

end SRWTightness
