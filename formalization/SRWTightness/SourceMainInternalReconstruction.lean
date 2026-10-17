import SRWTightness.SourceMainInternalBufferedDiskEmbedding
import SRWTightness.SourceMainInternalPositiveBridgeReversalReconstructed

open Filter MeasureTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_main_claims_internal_reconstruction [MeasurableSpace (List
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
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (hLower : GWBarrierLowerInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_positive_bridge_reversal_reconstructed
    hExt hErase hP hH hGW hBE
    hReflection hBridge
    hInitial hHit hLower
    hBDZ hSup hGreen buffered_dyadic_interior_disk_embedding_input_internal

end SRWTightness
