import SRWTightness.SourceConditionalRemainingUpper
import SRWTightness.SourceRemainingConditionalProbability
import SRWTightness.SourceEnlargedCountLower
import SRWTightness.SourceEventOriginalJointRootBound
import SRWTightness.SourceCapacityHalfProfile

open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.6 with an explicit error envelope: complete remaining successes are bounded
after summing against the original joint root-count law. Normalization follows from the cutoff. -/
theorem source_remaining_joint_root_bound (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
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
      ∀ G : Set ExteriorPathRecord,
      sourceEnlargedLaw.real
        {p | p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
          p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
          sourcePairExteriorRecord t b w ν J p.1 ∈ G ∧
          sourceActualCount t b ν p.1 ≤ sourceEarlyRootCap t ν ∧
          sourceActualCount t w ν p.1 ≤ sourceEarlyRootCap t ν} ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t) *
        ∫ ω, {u : Sample | sourcePairExteriorRecord t b w ν J u ∈ G ∧
            sourceActualCount t b ν u ≤ sourceEarlyRootCap t ν ∧
            sourceActualCount t w ν u ≤ sourceEarlyRootCap t ν}.indicator
          (fun u ↦ sourceContinuationProbability t A γ b I₀ z₀ ν (sourceActualCount t b ν u) *
            sourceContinuationProbability t A γ w I₁ z₁ ν (sourceActualCount t w ν u)) ω
          ∂pathLaw := by
  obtain ⟨D₁, C₁, B, W, J₁, hD₁, hC₁, hB, hW, hJ₁, hupper⟩ :=
    source_conditional_remaining_upper hExt hFlat hR hP hH hM hT
  obtain ⟨D₂, C₂, J₂, hD₂, hC₂, hJ₂, hlower⟩ :=
    source_enlarged_reference_count_lower hExt hFlat hR hP hH hM hT
  refine ⟨D₁ + D₂, C₁ + C₂, B, W, max J₁ J₂, add_pos hD₁ hD₂, add_pos hC₁ hC₂,
    hB, hW, hJ₁.trans (le_max_left _ _), ?_⟩
  filter_upwards [hupper, hlower, eventually_ge_atTop sourceCapacityHalfThreshold,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (70 : ℝ))]
    with t hu hl htcap hm
  intro b w ν J hb hw hbw hd hν hform hJ A γ I₀ I₁ z₀ z₁
    lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
    hγ ha₀ hc₀ ha₁ hc₁ G
  have hJu : J₁ ≤ (J : ℝ) := (le_max_left _ _).trans hJ
  have hJl : J₂ ≤ (J : ℝ) := (le_max_right _ _).trans hJ
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1.le
  have hcap₀ := (source_capacity_half_profile b t (A * diskEnergyGapRatio ^ I₀) _
    htcap ha₀ hc₀ (Finset.Subset.refl _)).trans (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hcap₁ := (source_capacity_half_profile w t (A * diskEnergyGapRatio ^ I₁) _
    htcap ha₁ hc₁ (Finset.Subset.refl _)).trans (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  let E := 16 * ((ν : ℝ) + 1) ^ 2 *
    (D₁ * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C₁ * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
    2 * sourceForestQuadraticError B W 8 t
  let F := 16 * ((ν : ℝ) + 1) ^ 2 *
    (D₂ * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C₂ * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14))
  have hbound := source_event_original_joint_root_bound t A γ b w I₀ I₁ ν J z₀ z₁
    hα hcap₀ hcap₁
    (sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∩
      sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν)
    G (sourceReferenceJointCountWeight t ν J) E F
  simp only [Set.mem_inter_iff, and_assoc] at hbound
  refine (hbound ?_ ?_).trans_eq ?_
  · intro h hh k l hk hlcap
    have hden := source_enlarged_path_event
      {ω | sourcePairExteriorRecord t b w ν J ω = h}
    simp only [Set.mem_setOf_eq] at hden
    have hhpath : 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} := by
      rwa [hden] at hh
    have hup := hu b w ν J hb hw hbw hd hν hform hJu A γ I₀ I₁ z₀ z₁
      hGW₀ hGW₁ hMix hα hcap₀ hcap₁ hγ ha₀ hc₀ ha₁ hc₁ h hhpath k l hk hlcap
    rw [source_remaining_conditional_probability] at hup
    exact hup
  · intro h hh k l hk hlcap
    exact hl b w ν J hb hw hbw hd hν hform hJl h hh k l hk hlcap
  · congr 2
    dsimp [E, F]
    ring

end SRWTightness
