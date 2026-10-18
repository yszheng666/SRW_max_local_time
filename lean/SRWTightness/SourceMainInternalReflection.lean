import SRWTightness.SourceMainInternalPositiveBridge
import SRWTightness.BridgeReflectionInternal

open Filter MeasureTheory
namespace SRWTightness

/-- Main claims with the original bridge reflection theorem proved from the actual
Gaussian paths. -/
theorem source_main_claims_internal_reflection
    [MeasurableSpace (List WordMark)] [MeasurableSingletonClass (List WordMark)]
    (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput)
    (hGW : GWBarrierUpperInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hLower : GWBarrierLowerInput)
    (hBDZ : BDZDyadicSquareMaximumInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_positive_bridge hP hH hGW hBE
    bridge_reflection_input_internal hLower hBDZ

end SRWTightness
