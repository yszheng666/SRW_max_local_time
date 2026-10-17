import SRWTightness.SourceMainInternalBesselInverseMoment
import SRWTightness.SourceMainInternalBesselElementaryReconstructed

open Filter MeasureTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_main_claims_internal_bessel_inverse_moment_reconstructed [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)]
    (hExt : ExteriorBridgeFactorizationInput)
    (hErase : ExteriorNestedCountInvarianceInput)
    (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput)
    (hGW : GWBarrierUpperInput)

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
  exact source_main_claims_internal_bessel_elementary_reconstructed
    hExt hErase hP hH hGW hBE
    hReflection hBridge hReverse
    hInitial hHit besselInverseMomentConstant bessel_three_inverse_moment_input_internal hLower
    hBDZ hSup hGreen hEmbed

end SRWTightness
