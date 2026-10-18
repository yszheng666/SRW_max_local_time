import SRWTightness.SourceEarlyCenteredPairEndpoint
import SRWTightness.SourceEarlyPairShellBound

open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.27, strengthened after a fixed threshold to a pure stretched-exponential bound. -/
theorem source_early_pair_shell_decay [MeasurableSpace (List WordMark)]
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
    (hIncrement : BesselThreeIncrementInput) :
    ∃ A : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧
      3 ≤ J₀ ∧ 2 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ a : ℕ, a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
      [∀ b : Site, MeasurableSpace
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSingletonClass
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSpace
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ b : Site, MeasurableSingletonClass
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ b : Site, MeasurableSpace (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [∀ b : Site, MeasurableSingletonClass (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hForest : ∀ b : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        MarkedGWForestJointInput
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix : ∀ b w : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        w ∈ sourceCandidateAnnulus (Real.exp t) → b ≠ w →
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      sourcePairShellMass t A (2 / 5) I a ≤ Real.exp (-(a : ℝ) ^ (2 / 5 : ℝ) / 2) := by
  classical
  obtain ⟨A, C, J₀, ap, hA, hC, hJ₀, hap, hp⟩ :=
    source_early_centered_pair_endpoint_bound hLast hrec hMarginal hJoint hExt hFlat hErase
      hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection hBridge hReverse
      hPositive hInitial hHit Cm hMoment hIncrement
  obtain ⟨as, has, hs⟩ := source_early_pair_shell_of_endpoint hDisk hAnnulus C hC J₀
  refine ⟨A, J₀, max ap as, hA, hJ₀, has.trans (le_max_right _ _), ?_⟩
  filter_upwards [hp, hs] with t hp hs
  intro a ha hrange
  dsimp only
  intro I hI cm cs clm cls lm ls rm rs fm fs hForest hMix
  apply hs A I a ((le_max_right _ _).trans ha) hrange
  intro p hpairs
  obtain ⟨hZ, hne, hindex⟩ := Finset.mem_filter.mp hpairs
  obtain ⟨hb, hw⟩ := Finset.mem_product.mp hZ
  have hpair := hp p.1 p.2 hb hw hne
  rw [← hindex] at hpair
  exact hpair ((le_max_left _ _).trans ha) hrange I hI
    (hForest p.1 hb) (hForest p.2 hw) (hMix p.1 p.2 hb hw hne)

end SRWTightness
