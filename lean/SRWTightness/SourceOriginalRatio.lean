import SRWTightness.SourceDiskSeed
import SRWTightness.SourceCanonicalRatio

open MeasureTheory Filter

namespace SRWTightness

/-- Source(9.18) with the literal second-moment ratio and constructed original-walk moments. -/
theorem source_original_ratio [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) (hErase : ExteriorNestedCountInvarianceInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) (hExit : FiniteKilledWalkMomentInput)
    (hGW : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (hLower : GWBarrierLowerInput)
    (hSum : SeparatedStretchedExponentialSumInput)
    (hBound : QuadraticStretchedExponentialBoundInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hEndpoint : GaussianEndpointResidualInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (hAllForest : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWForestJointInput (Mark K))
    (hAllMix : ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
      [MeasurableSpace (List α)] [MeasurableSpace (List β)]
      [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)],
      OrderedForestMixtureInput α β) :
    ∃ A c D : ℝ, 1 ≤ A ∧ 0 < c ∧ 0 < D ∧ 0 < c ^ 2 / D ∧ ∀ᶠ R : ℝ in atTop, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) /
        (Real.log R) ^ 6 ↔ i ≤ I) ∧
      let W := sourceCenteredSuccessCount (Real.log R) A (2 / 5) I
      0 < (∫ p, W p ∂sourceEnlargedLaw) ∧
      0 < (∫ p, W p ^ 2 ∂sourceEnlargedLaw) ∧
      c ^ 2 / D ≤ (∫ p, W p ∂sourceEnlargedLaw) ^ 2 /
        (∫ p, W p ^ 2 ∂sourceEnlargedLaw) ∧
      (∫ p, W p ∂sourceEnlargedLaw) ^ 2 / (∫ p, W p ^ 2 ∂sourceEnlargedLaw) ≤
        sourceEnlargedLaw.real {p | 0 < W p} ∧
      sourceEnlargedLaw.real {p | 0 < W p} ≤
        pathLaw.real {ω | diskCenter R ≤ Real.sqrt (diskMax R ω)} := by
  obtain ⟨A, hA, hMoments⟩ := source_original_moment_bounds hDisk hAnnulus hLast hrec
    hMarginal hJoint hExt hFlat hErase hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement hLower
    (fun K _ _ ↦ (hAllForest K).singleRoot) hSum hBound hKernel hEndpoint hOcc hRes
  have hA1 : 1 ≤ A := by
    have hh := diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA)
    linarith only [hh]
  obtain ⟨c, D, hc, hD, ht⟩ := source_canonical_ratio A hA1 hMoments hAllForest hAllMix
  refine ⟨A, c, D, hA1, hc, hD, div_pos (pow_pos hc 2) hD, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually ht, eventually_gt_atTop (0 : ℝ)]
    with R ht hR
  simpa only [Real.exp_log hR] using ht

end SRWTightness
