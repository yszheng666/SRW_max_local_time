import SRWTightness.SourceMainInternalExteriorBridges
import SRWTightness.BesselInitialFromDelayed

open Filter MeasureTheory

namespace SRWTightness

/-- Main claims deriving initial Bessel hitting from delayed hitting
and the sharp inverse moment. -/
theorem source_main_claims_internal_initial_hitting [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)]
    (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput)
    (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hHit : BesselThreeDelayedHittingInput)
    (hLower : GWBarrierLowerInput)


    (hBDZ : BDZDyadicSquareMaximumInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_exterior_bridges hP hH hGW hBE
    hReflection hBridge (besselThreeHittingInput_of_delayed hHit) hHit hLower hBDZ

end SRWTightness
