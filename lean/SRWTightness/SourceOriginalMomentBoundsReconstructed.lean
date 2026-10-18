import SRWTightness.SourceOriginalMomentBounds
import SRWTightness.SourceSharedRadiusEstimatesReconstructed

open MeasureTheory Filter

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_original_moment_bounds_reconstructed [MeasurableSpace (List WordMark)]
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
    (hLower : GWBarrierLowerInput)
    (hAllJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K))
    (hSum : SeparatedStretchedExponentialSumInput)
    (hBound : QuadraticStretchedExponentialBoundInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hEndpoint : GaussianEndpointResidualInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ A : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ SourceCanonicalMomentEstimate A := by
  let J := max sourcePairLogMargin
    (Real.log (4 * diskEnergyGapRatio) - sourceEquilibriumTimeError - sourceLowerTimeError)
  obtain ⟨A, hTerminal, hOne, hEarly, hFixed⟩ := source_shared_radius_estimates_reconstructed
    hDisk hAnnulus hLast hrec hMarginal hJoint hExt hFlat hErase hR hP hH hM hT hExit
    hGW hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm hMoment hIncrement J hLower hAllJoint
  obtain ⟨a, B, hA, hlog, ha, hB, ht⟩ := hTerminal
  have hTerminal : SourceTerminalEstimate J A (2 / 5) :=
    ⟨a, B, hA, hlog, ha, hB, ht⟩
  have hmargin : sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤
      Real.log A := by
    have hh : sourcePairLogMargin ≤ J := le_max_left _ _
    linarith only [hh, hlog]
  have hA0 : 0 < A := by
    have hh := diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA)
    linarith only [hh]
  have hAB : 4 * diskEnergyGapRatio ≤ A := by
    have hh : Real.log (4 * diskEnergyGapRatio) - sourceEquilibriumTimeError -
        sourceLowerTimeError ≤ J := le_max_right _ _
    have he := Real.exp_le_exp.mpr (show Real.log (4 * diskEnergyGapRatio) ≤ Real.log A by
      linarith only [hh, hlog])
    simpa only [Real.exp_log (show 0 < 4 * diskEnergyGapRatio by
      nlinarith [diskEnergyGapRatio_gt_four]), Real.exp_log hA0] using he
  have hLater := source_centered_late_common_bounded hSum hBound (2 / 5) (by norm_num)
    hDisk hAnnulus hP hGW hKernel hEndpoint hBE hMarginal hOcc hRes hAllJoint A hA hAB hmargin
  exact ⟨A, hA, source_canonical_moment_bounds J A hTerminal hOne hEarly hFixed hLater⟩

end SRWTightness
