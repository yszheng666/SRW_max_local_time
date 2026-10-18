import SRWTightness.SourceEarlyPairShellDecay
import SRWTightness.StretchedExponentialSummable

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- The total contribution of all moving early distance shells is uniformly bounded. -/
theorem source_early_pairs_uniform_sum [MeasurableSpace (List WordMark)]
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
    ∃ A C : ℝ, ∃ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
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
        sourcePairShellMass t A (2 / 5) I a) ≤ C := by
  classical
  obtain ⟨A, J₀, a₀, hA, hJ₀, ha₀, hp⟩ :=
    source_early_pair_shell_decay hDisk hAnnulus hLast hrec hMarginal hJoint hExt hFlat hErase
      hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection hBridge hReverse
      hPositive hInitial hHit Cm hMoment hIncrement
  have hsum : Summable (fun n : ℕ ↦ Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2)) := by
    convert stretched_exponential_summable (1 / 2) (2 / 5) (by norm_num) (by norm_num) using 1
    funext n
    congr 1
    ring
  let C := (∑' n : ℕ, Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2)) + 1
  have hC : 0 < C := by
    have hh : 0 ≤ ∑' n : ℕ, Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2) :=
      tsum_nonneg (fun n : ℕ ↦ (Real.exp_pos (-(n : ℝ) ^ (2 / 5 : ℝ) / 2)).le)
    dsimp only [C]
    linarith only [hh]
  refine ⟨A, C, a₀, hA, hC, ha₀, ?_⟩
  filter_upwards [hp] with t hp
  intro I hI cm cs clm cls lm ls rm rs fm fs hForest hMix
  calc
    _ ≤ ∑ a ∈ Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t),
        Real.exp (-(a : ℝ) ^ (2 / 5 : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, har⟩ := Finset.mem_Ico.mp ha
      exact hp a ha0 har I hI hForest
        (fun b w hb hw hne ↦ hMix b w (a + sourceEarlyDistanceGap a J₀ + 5) hb hw hne)
    _ ≤ ∑' n : ℕ, Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2) :=
      hsum.sum_le_tsum _ (fun n hn ↦ (Real.exp_pos _).le)
    _ ≤ C := le_add_of_nonneg_right (by norm_num)

end SRWTightness
