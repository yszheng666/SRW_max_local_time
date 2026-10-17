import SRWTightness.SourceMainInternalBesselHitting
import SRWTightness.PositiveBridgeRestrictionInternal

open Filter MeasureTheory
namespace SRWTightness

/-- Main claims with the complete original positive-bridge restriction input internally proved. -/
theorem source_main_claims_internal_positive_bridge
    [MeasurableSpace (List WordMark)] [MeasurableSingletonClass (List WordMark)]
    (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput)
    (hGW : GWBarrierUpperInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hReflection : BridgeReflectionInput)
    (hLower : GWBarrierLowerInput)
    (hBDZ : BDZDyadicSquareMaximumInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_bessel_hitting hP hH hGW hBE hReflection
    (positive_bridge_restriction_input_internal hReflection) hLower hBDZ

end SRWTightness
