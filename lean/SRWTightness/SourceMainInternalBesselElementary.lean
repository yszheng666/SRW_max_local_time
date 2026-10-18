import SRWTightness.SourceMainDerivedGaussianKernel
import SRWTightness.BesselThreePositiveInternal
import SRWTightness.BesselThreeIncrementInternal

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with deterministic Bessel positivity and the full
radial increment second-moment bound internally proved. Remaining inputs stay explicit. -/
theorem source_main_claims_internal_bessel_elementary [MeasurableSpace (List
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
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hLower : GWBarrierLowerInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_derived_gaussian_kernel
    hExt hErase hP hH hGW hReconstruct hBE
    hReflection hBridge hReverse
    bessel_three_positive_input_internal hInitial hHit Cm hMoment
    bessel_three_increment_input_internal hLower
    hBDZ hSup hGreen hEmbed

end SRWTightness
