import SRWTightness.SourceConditionalFineTuple
import SRWTightness.SourceFineBlockWeight
import SRWTightness.SourceReferenceParameter
import SRWTightness.OrderedTupleErrorDomination
import SRWTightness.SourceReferenceMixtureSuccess

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- The actual source conditional tuple measure is dominated by its fixed-total reference measure
on the region where the full record error is bounded. -/
theorem source_conditional_tuple_domination (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C B W J₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) → ∀ (a₀ a₁ : ℝ) (K₀ K₁ : Finset Site),
      ∀ [MeasurableSpace (SourceFineRecord t K₀ ν)]
        [MeasurableSingletonClass (SourceFineRecord t K₀ ν)]
        [MeasurableSpace (SourceFineRecord t K₁ ν)]
        [MeasurableSingletonClass (SourceFineRecord t K₁ ν)]
        [MeasurableSpace (List (SourceFineRecord t K₀ ν))]
        [MeasurableSingletonClass (List (SourceFineRecord t K₀ ν))]
        [MeasurableSpace (List (SourceFineRecord t K₁ ν))]
        [MeasurableSingletonClass (List (SourceFineRecord t K₁ ν))],
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 → K₀ ⊆ translateFinset b (diskFinset a₀) →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 → K₁ ⊆ translateFinset w (diskFinset a₁) →
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ (k l : ℕ) (E : ℝ),
      (sourceConditionalFineTupleLaw t b w K₀ K₁ ν J h).restrict
        (orderedTupleErrorRegion (fun i ↦ (h.1.get i).2.1) k l
          (fun r : Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν ↦
            ∑ i, sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J (r i)) E) ≤
        ENNReal.ofReal (Real.exp E) • orderedTaggedCountMeasure
          (sourceLongEscapeParameter (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
          (fun i ↦ (h.1.get i).2.1)
          (sourceFineReferenceMeasure t b K₀ ν) (sourceFineReferenceMeasure t w K₁ ν) k l := by
  obtain ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, hprod⟩ :=
    source_exterior_record_product hF hR hP hH hM hT
  refine ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hprod, source_reference_parameter_early] with t ht hparam
  intro b w ν J hb hw hbw hd hν hform hJ a₀ a₁ K₀ K₁
  intro m₀ s₀ m₁ s₁ lm₀ ls₀ lm₁ ls₁ ha₀ hc₀ hK₀ ha₁ hc₁ hK₁ h hh k l E
  letI := finiteExcursionRecord_countable (Mark K₀)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := finiteExcursionRecord_countable (Mark K₁)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := sourceConditionalFineTupleLaw_probability t b w K₀ K₁ ν J h hh
  have hJpos : 1 ≤ J := by exact_mod_cast (show (1 : ℝ) ≤ J by linarith)
  have hp := hparam ν J hν hJpos
  apply ordered_tuple_error_domination _ _ _ _ hp.1.le hp.2.le
  intro r hr
  have hcompat : ∀ i, sourceExteriorFineCompatible t K₀ K₁ ν (h.1.get i) (r i) := hr
  have hbnd := (ht b w ν J hb hw hbw hd hν hform hJ a₀ a₁ K₀ K₁
    ha₀ hc₀ hK₀ ha₁ hc₁ hK₁ h hh r hcompat).2
  rw [← sourceConditionalFineTupleLaw_atom t b w K₀ K₁ ν J h r] at hbnd
  simpa only [source_tagged_block_weight] using hbnd

end SRWTightness
