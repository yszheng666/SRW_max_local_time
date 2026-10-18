import SRWTightness.SourceMainInternalReconstruction
import SRWTightness.PlanarGaussianSupremumInternal

open Filter MeasureTheory

namespace SRWTightness

/-- Main claims using the proved uniform planar Gaussian supremum estimate. -/
theorem source_main_claims_internal_planar_supremum [MeasurableSpace (List
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


    (hBDZ : BDZDyadicSquareMaximumInput)


    (hGreen : BufferedSquareGreenInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_reconstruction hExt hErase hP hH hGW hBE
    hReflection hBridge hInitial hHit hLower hBDZ
    planarGaussianIncrementSupInput_internal hGreen

end SRWTightness
