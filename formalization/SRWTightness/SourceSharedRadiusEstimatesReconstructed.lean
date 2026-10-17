import SRWTightness.SourceSharedRadiusEstimates
import SRWTightness.SourceSharedPairBoundsReconstructed
import SRWTightness.SourceSharedTerminalBoundsReconstructed
import SRWTightness.SourceTerminalEstimateReconstructed

open MeasureTheory Filter
open scoped BigOperators Topology

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_shared_radius_estimates_reconstructed [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) (hErase : ExteriorNestedCountInvarianceInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) (hExit : FiniteKilledWalkMomentInput)
    (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (Jmargin : ℝ) (hLower : GWBarrierLowerInput)
    (hAllJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ A : ℝ, SourceTerminalEstimate Jmargin A (2 / 5) ∧
      SourceOnePointEstimate Jmargin A (2 / 5) ∧ SourceMovingEarlyEstimate A ∧
        SourceFixedPairsEstimate A (2 / 5) := by
  obtain ⟨A, hTerminal⟩ := source_terminal_estimate_exists_reconstructed Jmargin hBE hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm (2 / 5) hMoment hIncrement
    (by norm_num) (by norm_num)
  refine ⟨A, hTerminal, ?_, ?_, ?_⟩
  · exact source_onepoint_with_margin_shared_reconstructed Jmargin hP hLower hGW hBE
      hGaussian hReflection hBridge hReverse hPositive hInitial hHit Cm (2 / 5)
      hMoment hIncrement (by norm_num) (by norm_num) hAnnulus hAllJoint A hTerminal
  · exact source_early_pairs_uniform_sum_shared_reconstructed hDisk hAnnulus hLast hrec hMarginal
      hJoint
      hExt hFlat hErase hR hP hH hM hT hExit hGW hBE hGaussian hReflection
      hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement Jmargin A hTerminal
  · exact source_fixed_pairs_uniform_sum_shared_reconstructed hAnnulus hExt hFlat hR hP hH hM hT hGW
      hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
      Cm (2 / 5) hMoment hIncrement (by norm_num) (by norm_num) Jmargin A hTerminal

end SRWTightness
