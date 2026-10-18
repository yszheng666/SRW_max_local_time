import SRWTightness.SourceOriginalMomentBounds
import SRWTightness.SourceSeedFromMoments
import SRWTightness.LowerTailFromSeed

open MeasureTheory Filter
namespace SRWTightness

/-- The original SRW seed proposition follows from the completed source moments, with all
literature and generic forest interfaces retained as explicit conditions. -/
theorem source_disk_seed_claim [MeasurableSpace (List WordMark)]
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
    DiskSeedClaim := by
  obtain ⟨A, hA, hMoments⟩ := source_original_moment_bounds hDisk hAnnulus hLast hrec
    hMarginal hJoint hExt hFlat hErase hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement hLower
    (fun K _ _ ↦ (hAllForest K).singleRoot) hSum hBound hKernel hEndpoint hOcc hRes
  have hA1 : 1 ≤ A := by
    have hh := diskGaussianMinimumRadius_ge_four.trans
      (diskPointGaussianMinimumRadius_ge_base.trans hA)
    linarith only [hh]
  obtain ⟨p, hp, ht⟩ := source_seed_from_moments A hA1 hMoments hAllForest hAllMix
  have hlarge : ∀ᶠ R : ℝ in atTop,
      p ≤ pathLaw.real {ω | diskCenter R ≤ Real.sqrt (diskMax R ω)} := by
    filter_upwards [Real.tendsto_log_atTop.eventually ht, eventually_gt_atTop (0 : ℝ)]
      with R ht hR
    simpa only [Real.exp_log hR] using ht
  obtain ⟨Rstar, hRstar⟩ := eventually_atTop.mp hlarge
  exact ⟨p, hp, Rstar, hRstar⟩

/-- The lower-tail amplification now has the internally constructed seed on the original
walk, rather than an unproved source seed premise. -/
theorem source_disk_lower_tail [MeasurableSpace (List WordMark)]
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
    ∃ c s₀ : ℝ, 0 < c ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real {ω | diskFluctuation R ω < -s}) atTop ≤
        Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 4)) := by
  exact disk_lower_tail_of_seed (source_disk_seed_claim hDisk hAnnulus hLast hrec hMarginal
    hJoint hExt hFlat hErase hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection
    hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement hLower hSum hBound hKernel
    hEndpoint hOcc hRes hAllForest hAllMix)

end SRWTightness
