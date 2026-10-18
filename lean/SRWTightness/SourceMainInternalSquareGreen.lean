import SRWTightness.SourceMainInternalPlanarSupremum
import SRWTightness.BufferedSquareGreenInternal

open Filter MeasureTheory

namespace SRWTightness

/-- Main claims deriving the buffered-square Green estimates from the existing Harnack input. -/
theorem source_main_claims_internal_square_green [MeasurableSpace (List
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


    (hBDZ : BDZDyadicSquareMaximumInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_planar_supremum hExt hErase hP hH hGW hBE
    hReflection hBridge hInitial hHit hLower hBDZ
    (bufferedSquareGreenInput_of_positiveHarmonic hH)

end SRWTightness
