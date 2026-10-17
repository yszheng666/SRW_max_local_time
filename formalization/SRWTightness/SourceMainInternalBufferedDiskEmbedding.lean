import SRWTightness.SourceMainInternalPositiveBridgeReversal
import SRWTightness.BufferedInteriorDiskEmbeddingInternal

open Filter MeasureTheory

namespace SRWTightness

/-- All five original-walk endpoints with the complete buffered dyadic enclosure geometry
proved internally. Other remaining inputs stay explicit. -/
theorem source_main_claims_internal_buffered_disk_embedding [MeasurableSpace (List
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


    (hGreen : BufferedSquareGreenInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_positive_bridge_reversal
    hExt hErase hP hH hGW hReconstruct hBE
    hReflection hBridge
    hInitial hHit hLower
    hBDZ hSup hGreen buffered_dyadic_interior_disk_embedding_input_internal

end SRWTightness
