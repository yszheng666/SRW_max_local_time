import SRWTightness.SourceDiskSeed
import SRWTightness.LowerTailPowerFromSeed

open MeasureTheory Filter

namespace SRWTightness

/-- Both inequalities in source(10.5) follow from the constructed original-walk seed. -/
theorem source_disk_lower_power [MeasurableSpace (List WordMark)]
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
    ∃ p c s₀ : ℝ, 0 < p ∧ p ≤ 1 ∧ 0 < c ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real
        {ω | Real.sqrt (diskMax R ω) < diskCenter R - s}) atTop ≤
        (1 - p) ^ (amplificationScale s / 2) ∧
      (1 - p) ^ (amplificationScale s / 2) ≤
        Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 4)) := by
  obtain ⟨p, c, s₀, hp, hp1, hc, hs₀, ht⟩ :=
    disk_lower_tail_power_of_seed (source_disk_seed_claim hDisk hAnnulus hLast hrec
    hMarginal hJoint hExt hFlat hErase hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement hLower
    hSum hBound hKernel hEndpoint hOcc hRes hAllForest hAllMix)
  refine ⟨p, c, s₀, hp, hp1, hc, hs₀, ?_⟩
  intro s hs
  have he (R : ℝ) : {ω | diskFluctuation R ω < -s} =
      {ω | Real.sqrt (diskMax R ω) < diskCenter R - s} := by
    ext ω
    change (Real.sqrt (diskMax R ω) - diskCenter R < -s) ↔
      Real.sqrt (diskMax R ω) < diskCenter R - s
    constructor <;> intro h <;> linarith
  simpa only [he] using ht s hs

end SRWTightness
