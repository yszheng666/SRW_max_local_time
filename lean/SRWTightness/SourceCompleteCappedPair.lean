import SRWTightness.SourceAllDistanceExterior
import SRWTightness.SourceCompleteRemainingInclusion

open MeasureTheory Filter
namespace SRWTightness

/-- The full two-site event is bounded by the capped continuation product at every distance
index, including zero; no exterior prefix condition is required. -/
theorem source_complete_capped_pair_bound_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ D C B W J₀ : ℝ, 0 < D ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
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
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I₀ z₀ ∩ sourceSiteSuccessEvent t A γ w I₁ z₁) ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t) *
        ∫ ω, {u : Sample | sourceActualCount t b ν u ≤ sourceEarlyRootCap t ν ∧
            sourceActualCount t w ν u ≤ sourceEarlyRootCap t ν}.indicator
          (fun u ↦ sourceContinuationProbability t A γ b I₀ z₀ ν (sourceActualCount t b ν u) *
            sourceContinuationProbability t A γ w I₁ z₁ ν (sourceActualCount t w ν u)) ω
          ∂pathLaw := by
  obtain ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, hbound⟩ :=
    source_remaining_joint_root_bound_all_indices hExt hFlat hR hP hH hM hT
  refine ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hbound, source_complete_remaining_inclusion hFlat] with t ht hinc
  intro b w ν J hb hw hbw hν hform hJ A γ I₀ I₁ z₀ z₁
    lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
    hγ ha₀ hc₀ ha₁ hc₁
  have hbnd := ht b w ν J hb hw hbw hν hform hJ A γ I₀ I₁ z₀ z₁
    hGW₀ hGW₁ hMix hγ ha₀ hc₀ ha₁ hc₁ Set.univ
  have hevent : ∀ᵐ p ∂sourceEnlargedLaw,
      p ∈ sourceSiteSuccessEvent t A γ b I₀ z₀ ∩ sourceSiteSuccessEvent t A γ w I₁ z₁ →
      p ∈ {p | p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
        p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
        sourcePairExteriorRecord t b w ν J p.1 ∈ Set.univ ∧
        sourceActualCount t b ν p.1 ≤ sourceEarlyRootCap t ν ∧
        sourceActualCount t w ν p.1 ≤ sourceEarlyRootCap t ν} := by
    filter_upwards [hinc A γ b w I₀ I₁ 0 ν z₀ z₁ hγ ha₀ hc₀ ha₁ hc₁ hb hw (Nat.zero_le ν) hν]
      with p hp
    intro hs
    obtain ⟨h₀, h₁, hpref, hc₀, hc₁⟩ := hp hs
    exact ⟨h₀, h₁, Set.mem_univ _, hc₀, hc₁⟩
  have hprob := ENNReal.toReal_mono (measure_ne_top sourceEnlargedLaw _)
    (measure_mono_ae
      (s := sourceSiteSuccessEvent t A γ b I₀ z₀ ∩ sourceSiteSuccessEvent t A γ w I₁ z₁)
      hevent)
  simpa only [Measure.real, Set.mem_univ, true_and] using hprob.trans hbnd

end SRWTightness
