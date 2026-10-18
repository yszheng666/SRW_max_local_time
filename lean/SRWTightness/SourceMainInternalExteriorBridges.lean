import SRWTightness.SourceMainInternalExteriorCounts
import SRWTightness.ExteriorBridgeFactorizationInternal

open Filter MeasureTheory

namespace SRWTightness

/-- Main claims using the internally proved full exterior bridge factorization. -/
theorem source_main_claims_internal_exterior_bridges [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)]
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
  exact source_main_claims_internal_exterior_counts
    exteriorBridgeFactorizationInput_internal hP hH hGW hBE
    hReflection hBridge hInitial hHit hLower hBDZ

end SRWTightness
