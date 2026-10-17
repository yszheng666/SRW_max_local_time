import SRWTightness.SourceMainInternalBesselElementary
import SRWTightness.BesselInverseMomentInternal

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with the actual radial inverse-moment bound
and its fixed universal constant internally proved. Other remaining inputs stay explicit. -/
theorem source_main_claims_internal_bessel_inverse_moment [MeasurableSpace (List
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
    (hReverse : PositiveBridgeReversalInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (hLower : GWBarrierLowerInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_bessel_elementary
    hExt hErase hP hH hGW hReconstruct hBE
    hReflection hBridge hReverse
    hInitial hHit besselInverseMomentConstant bessel_three_inverse_moment_input_internal hLower
    hBDZ hSup hGreen hEmbed

end SRWTightness
