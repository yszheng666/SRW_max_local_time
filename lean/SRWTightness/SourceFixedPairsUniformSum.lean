import SRWTightness.SourceFixedCenteredPair
import SRWTightness.SourceFixedPairSumBound

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- Equation 8.28: all candidate pairs in any fixed bounded distance-index range have a
uniformly bounded total contribution, including macroscopic separations. -/
theorem source_fixed_pairs_uniform_sum (hAnnulus : LatticeAnnulusCountInput)
    (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput)
    (hGW : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    :
    ∃ A : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ ∀ a₀ : ℕ,
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
        C := by
  obtain ⟨A, hA, hp⟩ := source_fixed_centered_pair_bound hExt hFlat hR hP hH hM hT
    hGW hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  obtain ⟨c, N, hc, hN, hcount⟩ := hAnnulus
  refine ⟨A, hA, ?_⟩
  intro a₀
  obtain ⟨C, hC, ν, hp⟩ := hp a₀
  refine ⟨N ^ 2 * C, mul_pos (pow_pos hN 2) hC, ?_⟩
  filter_upwards [hp, Real.tendsto_exp_atTop.eventually hcount] with t hp hn
  intro I hI lm ls rm rs fm fs hForest hMix
  exact source_fixed_pair_sum_bound t A γ C N I a₀ hC.le hN.le hn.2
    (fun b w hb hw hbw ha ↦
      hp b w hb hw hbw ha I hI (hForest b hb) (hForest w hw) (hMix b w ν hb hw hbw))

end SRWTightness
