import SRWTightness.SourceCompleteJointRootBound
import SRWTightness.SourceContinuationIntegralBound
import SRWTightness.SourceDecouplingExponent

open MeasureTheory Filter
namespace SRWTightness

/-- Complete two-site success is bounded by the original uncapped joint root exponential moment.
The prefix representation and continuation envelope are explicit intermediate obligations. -/
theorem source_complete_uncapped_root_bound (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) (hExit : FiniteKilledWalkMomentInput) :
    ∃ D C B W J₀ : ℝ, 0 < D ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) → ∀ (A γ : ℝ) (I₀ I₁ : ℕ)
        (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))
      (hγ : 0 ≤ γ),
      1 ≤ A * diskEnergyGapRatio ^ I₀ →
      A * diskEnergyGapRatio ^ I₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ A * diskEnergyGapRatio ^ I₁ →
      A * diskEnergyGapRatio ^ I₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ (j : ℕ) (G : Set ExteriorPathRecord), j ≤ ν →
      sourceEarlyPrefixEvent t b j = sourcePairExteriorRecord t b w ν J ⁻¹' G →
      ∀ C₀ : ℝ, 0 ≤ C₀ →
      (∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
        sourceContinuationProbability t A γ b I₀ z₀ ν k *
          sourceContinuationProbability t A γ w I₁ z₁ ν l ≤
        C₀ * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
          Real.exp (2 * Real.sqrt (2 * (k : ℝ)) + 2 * Real.sqrt (2 * (l : ℝ)))) →
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I₀ z₀ ∩ sourceSiteSuccessEvent t A γ w I₁ z₁) ≤
        Real.exp (sourceDecouplingExponent D C B W t ν J) *
          (C₀ * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
            ∫ ω, (sourceEarlyPrefixEvent t b j).indicator (fun u ↦ Real.exp
              (2 * Real.sqrt (2 * (sourceActualCount t b ν u : ℝ)) +
                2 * Real.sqrt (2 * (sourceActualCount t w ν u : ℝ)))) ω ∂pathLaw) := by
  obtain ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, hbound⟩ :=
    source_complete_joint_root_bound hExt hFlat hR hP hH hM hT
  refine ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hbound, source_continuation_integral_upper_bound hFlat hExit]
    with t ht hint
  intro b w ν J hb hw hbw hd hν hform hJ A γ I₀ I₁ z₀ z₁
    lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
    hγ ha₀ hc₀ ha₁ hc₁ j G hj hG C₀ hC₀ hprod
  have hbnd := ht b w ν J hb hw hbw hd hν hform hJ A γ I₀ I₁ z₀ z₁
    hGW₀ hGW₁ hMix hγ ha₀ hc₀ ha₁ hc₁ j G hj hG
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  have hZ : Measurable (sourcePairExteriorRecord t b w ν J) :=
    measurable_killedExteriorRecord _ _ _ _ _
  have hS : MeasurableSet (sourceEarlyPrefixEvent t b j) := by
    rw [hG]
    exact hZ MeasurableSpace.measurableSet_top
  exact hbnd.trans (mul_le_mul_of_nonneg_left
    (hint b w hb hw ν hν A γ C₀ I₀ I₁ z₀ z₁ hC₀ hprod _ hS) (Real.exp_pos _).le)

end SRWTightness
