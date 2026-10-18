import SRWTightness.SourceMainInternalGaussianInterval
import SRWTightness.FiniteGaussianBridgeKernelDerived

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with the finite Gaussian kernel derived from the
existing reconstruction and reflection inputs, preserving their explicit scopes. -/
theorem source_main_claims_derived_gaussian_kernel [MeasurableSpace (List
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
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (hLower : GWBarrierLowerInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_gaussian_interval
    hExt hErase hP hH hGW hReconstruct hBE
    hReflection hBridge hReverse
    hPositive hInitial hHit Cm hMoment hIncrement hLower
    (finite_gaussian_bridge_kernel_from_reconstruction_reflection hReconstruct hReflection)
    hBDZ hSup hGreen hEmbed

end SRWTightness
