import SRWTightness.SourceSharedPairBounds

open MeasureTheory Filter
open scoped BigOperators Topology
namespace SRWTightness

/-- The already proved source estimate, packaged while retaining its chosen radius. -/
def SourceOnePointEstimate (J A γ : ℝ) : Prop :=
    ∃ c C c₁ C₁ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧
      0 < c ∧ 0 < C ∧ 0 < c₁ ∧ 0 < C₁ ∧ ∀ᶠ R : ℝ in atTop,
      ∃ (I : sourceCandidateAnnulus R → ℕ)
        (z : ∀ b : sourceCandidateAnnulus R,
          translateFinset (b : Site) (diskFinset (A * diskEnergyGapRatio ^ I b))),
      (∀ b : sourceCandidateAnnulus R, (z b : Site) = (b : Site)) ∧
      (∀ (b : sourceCandidateAnnulus R) (i : ℕ),
        A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I b) ∧
      (∀ b : sourceCandidateAnnulus R,
        c * (R ^ 2)⁻¹ ≤ sourceEnlargedLaw.real
          (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ∧
        sourceEnlargedLaw.real (sourceSiteSuccessEvent (Real.log R) A γ b (I b) (z b)) ≤
          C * (R ^ 2)⁻¹) ∧
      c₁ ≤ (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ∧
        (∫ p, sourceSuccessCount R A γ I z p ∂sourceEnlargedLaw) ≤ C₁

/-- The already proved source estimate, packaged while retaining its chosen radius. -/
def SourceMovingEarlyEstimate (A : ℝ) : Prop :=
    ∃ C : ℝ, ∃ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      2 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [∀ j : ℕ, MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [∀ j : ℕ, MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [∀ j : ℕ, MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [∀ j : ℕ, MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
      [∀ b : Site, MeasurableSpace
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSingletonClass
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hForest : ∀ b : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        MarkedGWForestJointInput
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix : ∀ (b w : Site) (ν : ℕ), b ∈ sourceCandidateAnnulus (Real.exp t) →
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
      (∑ a ∈ Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t),
        sourcePairShellMass t A (2 / 5) I a) ≤ C

/-- The already proved source estimate, packaged while retaining its chosen radius. -/
def SourceFixedPairsEstimate (A γ : ℝ) : Prop :=
    diskPointGaussianMinimumRadius ≤ A ∧ ∀ a₀ : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [∀ b : Site, MeasurableSpace
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSingletonClass
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hForest : ∀ b : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        MarkedGWForestJointInput
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix : ∀ (b w : Site) (ν : ℕ), b ∈ sourceCandidateAnnulus (Real.exp t) →
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
      (∑ p ∈ sourceFixedDistancePairs t a₀, sourceEnlargedLaw.real
        (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I)) ≤
        C

/-- One internally chosen radius simultaneously supports the first moment and both early
pair regimes. No equality between independently chosen existential witnesses is assumed. -/
theorem source_shared_radius_estimates [MeasurableSpace (List WordMark)]
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
    (Jmargin : ℝ) (hLower : GWBarrierLowerInput)
    (hAllJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ A : ℝ, SourceTerminalEstimate Jmargin A (2 / 5) ∧
      SourceOnePointEstimate Jmargin A (2 / 5) ∧ SourceMovingEarlyEstimate A ∧
        SourceFixedPairsEstimate A (2 / 5) := by
  obtain ⟨A, hTerminal⟩ := source_terminal_estimate_exists Jmargin hReconstruct hBE hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm (2 / 5) hMoment hIncrement
    (by norm_num) (by norm_num)
  refine ⟨A, hTerminal, ?_, ?_, ?_⟩
  · exact source_onepoint_with_margin_shared Jmargin hP hLower hGW hReconstruct hBE
      hGaussian hReflection hBridge hReverse hPositive hInitial hHit Cm (2 / 5)
      hMoment hIncrement (by norm_num) (by norm_num) hAnnulus hAllJoint A hTerminal
  · exact source_early_pairs_uniform_sum_shared hDisk hAnnulus hLast hrec hMarginal hJoint
      hExt hFlat hErase hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection
      hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement Jmargin A hTerminal
  · exact source_fixed_pairs_uniform_sum_shared hAnnulus hExt hFlat hR hP hH hM hT hGW
      hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
      Cm (2 / 5) hMoment hIncrement (by norm_num) (by norm_num) Jmargin A hTerminal

end SRWTightness
