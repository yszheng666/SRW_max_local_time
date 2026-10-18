import SRWTightness.SourceRemainingUpperComparison
import SRWTightness.SourceRemainingEventImage
import SRWTightness.SourceConditionalRemainingRegion
import SRWTightness.SourceConditionalTupleDomination

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- The actual conditional remaining-success upper comparison, including terminal bridges.
All actual-path region and image premises are discharged from the source geometry. -/
theorem source_conditional_remaining_upper (hExt : ExteriorBridgeFactorizationInput)
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
      (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
      (hcap₀ : sourceReferenceIntensity (sourceLowerRadius t) 14 *
        capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ≤ 1)
      (hcap₁ : sourceReferenceIntensity (sourceLowerRadius t) 14 *
        capacity (translateFinset w (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ≤ 1)
      (hγ : 0 ≤ γ),
      1 ≤ A * diskEnergyGapRatio ^ I₀ →
      A * diskEnergyGapRatio ^ I₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ A * diskEnergyGapRatio ^ I₁ →
      A * diskEnergyGapRatio ^ I₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      (ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h}).real
        {p | p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
          p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
          sourceActualCount t b ν p.1 = k ∧ sourceActualCount t w ν p.1 = l} ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t) *
        (sourceReferenceJointCountWeight t ν J h k l *
          (sourceContinuationProbability t A γ b I₀ z₀ ν k *
            sourceContinuationProbability t A γ w I₁ z₁ ν l)) := by
  obtain ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, hdom⟩ :=
    source_conditional_tuple_domination hExt hR hP hH hM hT
  refine ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hdom, source_conditional_remaining_region hExt hFlat B W hB hW,
    source_conditional_remaining_event_image hExt hFlat, source_reference_parameter_early,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    eventually_ge_atTop (0 : ℝ)] with t hd hregion himage hparam hN htime ht0
  intro b w ν J hb hw hbw hdist hν hform hJ A γ I₀ I₁ z₀ z₁
    lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
    hα hcap₀ hcap₁ hγ ha₀ hc₀ ha₁ hc₁ h hh k l hk hl
  have hnreal : (ν : ℝ) ≤
      ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by
    exact_mod_cast hnreal
  have hdepth : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  have hJpos : 1 ≤ J := by exact_mod_cast (show (1 : ℝ) ≤ J by linarith)
  have hp := hparam ν J hν hJpos
  let K₀ := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))
  let K₁ := translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))
  let E := 16 * ((ν : ℝ) + 1) ^ 2 *
    (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
    2 * sourceForestQuadraticError B W 8 t
  let G := orderedTupleErrorRegion (fun i : Fin h.1.length ↦ (h.1.get i).2.1) k l
    (fun r : Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν ↦
      ∑ i, sourceExteriorFineError D C B W t (A * diskEnergyGapRatio ^ I₀)
        (A * diskEnergyGapRatio ^ I₁) K₀ K₁ ν J (r i)) E
  apply source_conditional_remaining_upper_of_domination t A γ b w I₀ I₁ ν J z₀ z₁
    hGW₀ hGW₁ hMix hα hcap₀ hcap₁ hγ hp.1.le hp.2.le h k l E hbw hh G
  · exact hd b w ν J hb hw hbw hdist hν hform hJ
      (A * diskEnergyGapRatio ^ I₀) (A * diskEnergyGapRatio ^ I₁) K₀ K₁
      ha₀ hc₀ (Finset.Subset.refl _) ha₁ hc₁ (Finset.Subset.refl _) h hh k l E
  · have hr := hregion b w ν J hb hw hbw hdist hν hform hdepth D C
      (A * diskEnergyGapRatio ^ I₀) (A * diskEnergyGapRatio ^ I₁) K₀ K₁ hD.le hC.le
      ha₀ hc₀ ha₁ hc₁ h hh k l hk hl
    have hi := himage b w ν J hb hw hbw hdist hν hform A γ I₀ I₁ z₀ z₁
      ha₀ hc₀ h hh k l
    filter_upwards [hr, hi] with p hrp hip
    rintro ⟨hs₀, hs₁, hx, hy⟩
    exact ⟨hrp hx hy hs₀.2.1 hs₁.2.1, hip hs₀ hs₁ hx hy⟩

end SRWTightness
