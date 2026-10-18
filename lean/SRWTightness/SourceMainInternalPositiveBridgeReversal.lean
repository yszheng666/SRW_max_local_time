import SRWTightness.SourceMainInternalBesselInverseMoment
import SRWTightness.PositiveBridgeReversalInternal

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with actual positive bridge reversal proved internally.
Other remaining inputs stay explicit. -/
theorem source_main_claims_internal_positive_bridge_reversal [MeasurableSpace (List
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
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (hLower : GWBarrierLowerInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_bessel_inverse_moment
    hExt hErase hP hH hGW hReconstruct hBE
    hReflection hBridge positive_bridge_reversal_input_internal
    hInitial hHit hLower
    hBDZ hSup hGreen hEmbed

end SRWTightness
