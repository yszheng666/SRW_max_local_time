import SRWTightness.SourceRemainingEventMeasurable
import SRWTightness.SourceConditionalTupleAuxiliary
import SRWTightness.OrderedReferenceMixtureMass
import SRWTightness.RestrictedEventComparison

open MeasureTheory
namespace SRWTightness

/-- Actual conditional remaining success is bounded by the same reference count weight and the
original continuation probabilities, once the verified region and image premises are supplied. -/
theorem source_conditional_remaining_upper_of_domination (t A γ : ℝ) (b w : Site) (I₀ I₁ ν J : ℕ)
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
    (hγ : 0 ≤ γ)
    (hp : 0 ≤ sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
    (hp₁ : sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J ≤ 1)
    (h : ExteriorPathRecord) (k l : ℕ) (E : ℝ) (hbw : b ≠ w)
    (hh : 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}) :
    let K₀ := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))
    let K₁ := translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))
    let μ := ProbabilityTheory.cond sourceEnlargedLaw
      {p | sourcePairExteriorRecord t b w ν J p.1 = h}
    let η := sourceConditionalFineTupleLaw t b w K₀ K₁ ν J h
    let ξ := orderedTaggedCountMeasure
      (sourceLongEscapeParameter (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
      (fun i ↦ (h.1.get i).2.1)
      (sourceFineReferenceMeasure t b K₀ ν) (sourceFineReferenceMeasure t w K₁ ν) k l
    let S := {p | p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
      p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
      sourceActualCount t b ν p.1 = k ∧ sourceActualCount t w ν p.1 = l}
    ∀ G : Set (Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν),
    η.restrict G ≤ ENNReal.ofReal (Real.exp E) • ξ →
    (∀ᵐ p ∂μ, p ∈ S → sourceFineTuple t b w K₀ K₁ ν J h p.1 ∈ G ∧
      (sourceFineTuple t b w K₀ K₁ ν J h p.1, (p.2 b, p.2 w)) ∈
        sourceTaggedRemainingEvent t A γ b w I₀ I₁ ν z₀ z₁ h k l) →
    μ.real S ≤ Real.exp E * (sourceReferenceJointCountWeight t ν J h k l *
      (sourceContinuationProbability t A γ b I₀ z₀ ν k *
        sourceContinuationProbability t A γ w I₁ z₁ ν l)) := by
  dsimp only
  intro G hdom hS
  let K₀ := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))
  let K₁ := translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))
  let σ := (independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ)
  let ξ := orderedTaggedCountMeasure
    (sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
    (fun i ↦ (h.1.get i).2.1)
    (sourceFineReferenceMeasure t b K₀ ν) (sourceFineReferenceMeasure t w K₁ ν) k l
  letI := finiteExcursionRecord_countable (Mark K₀)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := finiteExcursionRecord_countable (Mark K₁)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := sourceFineReferenceMeasure_probability t b K₀ ν
    (markedGWJoint_population hGW₀.singleRoot) hα hcap₀
  letI := sourceFineReferenceMeasure_probability t w K₁ ν
    (markedGWJoint_population hGW₁.singleRoot) hα hcap₁
  letI : IsFiniteMeasure ξ := ordered_reference_mixture_finite hMix _ _ _ hp hp₁ _ _ k l
  letI := sourceConditionalFineTupleLaw_probability t b w K₀ K₁ ν J h hh
  have haux : ((sourceConditionalFineTupleLaw t b w K₀ K₁ ν J h).prod σ).restrict
      (G ×ˢ Set.univ) ≤ ENNReal.ofReal (Real.exp E) • (ξ.prod σ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ, ← Measure.prod_smul_left]
    exact Measure.prod_mono hdom le_rfl
  have hf := source_conditional_tuple_auxiliary_preserving t b w K₀ K₁ ν J h hbw hh
  have hu := restricted_event_comparison_real _ _ (ξ.prod σ) _ hf
    (G ×ˢ Set.univ) (sourceTaggedRemainingEvent t A γ b w I₀ I₁ ν z₀ z₁ h k l)
    ((Set.to_countable G).measurableSet.prod MeasurableSet.univ)
    (sourceTaggedRemainingEvent_measurable t A γ b w I₀ I₁ ν z₀ z₁ h k l)
    E haux _ (hS.mono (fun p hp hmem ↦ ⟨⟨(hp hmem).1, Set.mem_univ _⟩, (hp hmem).2⟩))
  have hmass := source_reference_mixture_success t A γ b w I₀ I₁ ν J z₀ z₁
    hGW₀ hGW₁ hMix hα hcap₀ hcap₁ hγ hp hp₁ h k l
  change (ξ.prod σ).real (sourceTaggedRemainingEvent t A γ b w I₀ I₁ ν z₀ z₁ h k l) = _
    at hmass
  rw [hmass] at hu
  exact hu

end SRWTightness
