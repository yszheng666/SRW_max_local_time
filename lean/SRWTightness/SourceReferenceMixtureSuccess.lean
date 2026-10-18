import SRWTightness.SourceFineReferenceMeasure
import SRWTightness.OrderedForestMixtureAuxiliary
import SRWTightness.SourceContinuationForestProbability
import SRWTightness.SourceForestContinuationCoordinates
import SRWTightness.SourceReferenceCountLower

open MeasureTheory
namespace SRWTightness

/-- The source fine-record type at the remaining continuation depth. -/
abbrev SourceFineRecord (t : ℝ) (K : Finset Site) (ν : ℕ) :=
  FiniteExcursionRecord (Mark K)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))

/-- The reference tagged mixture, with both auxiliary bridge families integrated, gives the same
finite Q used in the count lower comparison times the two original continuation probabilities. -/
theorem source_reference_mixture_success (t A γ : ℝ) (b w : Site) (I₀ I₁ ν J : ℕ)
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
    (h : ExteriorPathRecord) (k l : ℕ) :
    let K₀ := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))
    let K₁ := translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))
    let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)
    let p := sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J
    ((orderedTaggedCountMeasure p (fun i ↦ (h.1.get i).2.1)
      (sourceFineReferenceMeasure t b K₀ ν) (sourceFineReferenceMeasure t w K₁ ν) k l).prod
        ((independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ))).real
      {q | ((orderedTaggedForests q.1).1, q.2.1) ∈
        sourceContinuationForestEvent t A γ b I₀ z₀ ν n k ∧
        ((orderedTaggedForests q.1).2, q.2.2) ∈ sourceContinuationForestEvent t A γ w I₁ z₁ ν n l} =
      sourceReferenceJointCountWeight t ν J h k l *
        (sourceContinuationProbability t A γ b I₀ z₀ ν k *
          sourceContinuationProbability t A γ w I₁ z₁ ν l) := by
  dsimp only
  letI := finiteExcursionRecord_countable
    (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))))
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := finiteExcursionRecord_countable
    (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))))
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := sourceFineReferenceMeasure_probability t b _ ν
    (markedGWJoint_population hGW₀.singleRoot) hα hcap₀
  letI := sourceFineReferenceMeasure_probability t w _ ν
    (markedGWJoint_population hGW₁.singleRoot) hα hcap₁
  rw [ordered_mixture_success_probability hMix _ _ _ _ _ hp hp₁ _ _ k l _ _
    (sourceContinuationForestEvent_measurable _ _ _ _ _ _ _ _ _)
    (sourceContinuationForestEvent_measurable _ _ _ _ _ _ _ _ _)]
  simp only [sourceFineReferenceMeasure]
  rw [source_continuation_forest_probability t A γ b I₀ z₀ ν _ k
    (source_fine_continuation_depth t ν) hGW₀ hα hcap₀ hγ,
    source_continuation_forest_probability t A γ w I₁ z₁ ν _ l
    (source_fine_continuation_depth t ν) hGW₁ hα hcap₁ hγ]
  rfl

end SRWTightness
