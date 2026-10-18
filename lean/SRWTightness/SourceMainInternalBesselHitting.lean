import SRWTightness.SourceMainInternalInitialHitting
import SRWTightness.BesselDelayedHittingInternal

open Filter MeasureTheory

namespace SRWTightness

/-- Main claims with both complete original Bessel hitting inputs internally proved. -/
theorem source_main_claims_internal_bessel_hitting [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)]
    (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput)
    (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hLower : GWBarrierLowerInput)


    (hBDZ : BDZDyadicSquareMaximumInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_initial_hitting hP hH hGW hBE
    hReflection hBridge besselThreeDelayedHittingInput_internal hLower hBDZ

end SRWTightness
