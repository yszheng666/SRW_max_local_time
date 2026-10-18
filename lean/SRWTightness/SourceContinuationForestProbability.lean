import SRWTightness.MarkedGWForestJointAuxiliary
import SRWTightness.SourceContinuationForestEvent

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The arbitrary-root reference forest success probability is the original source continuation probability. -/
theorem source_continuation_forest_probability (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ν n k : ℕ) (hn : n = sourceContinuationLength t ν)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    (hjoint : MarkedGWForestJointInput
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ≤ 1)
    (hγ : 0 ≤ γ)
    [MeasurableSpace (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n)]
    [MeasurableSingletonClass (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n)]
    [MeasurableSpace (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))] :
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let μ := finiteRecordReferenceMeasure (referenceMarkLaw D K α) n
    ((independentForestLaw μ k).prod (independentBridgeLaw ℕ)).real
      (sourceContinuationForestEvent t A γ b I z ν n k) = sourceContinuationProbability t A γ b I z ν k := by
  dsimp only
  by_cases hk : k = 0
  · simp [sourceContinuationForestEvent, sourceContinuationProbability, hk]
  rw [sourceContinuationProbability, if_neg hk, ← hn]
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let ρ := referenceMarkLaw D K α
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hh := markedGWForestJoint_auxiliary hjoint ρ (independentBridgeLaw ℕ) n k
    (sourceContinuationBand t ν n)
    (fun g ↦ sourceTerminalListBridgeEvent t A γ b I z (geometricGWPopulation g n))
    (fun g ↦ sourceTerminalListBridgeEvent_measurable t A γ b I z (geometricGWPopulation g n))
    (markedGWForestEvent_measurable n (sourceContinuationBand t ν n)
      (fun g ↦ sourceTerminalListBridgeEvent t A γ b I z (geometricGWPopulation g n))
      (fun g ↦ sourceTerminalListBridgeEvent_measurable t A γ b I z (geometricGWPopulation g n)))
  change ((independentForestLaw (finiteRecordReferenceMeasure ρ n) k).prod
    (independentBridgeLaw ℕ) (sourceContinuationForestEvent t A γ b I z ν n k)).toReal = _
  simp only [sourceContinuationForestEvent, ne_eq, hk, not_false_eq_true, true_and]
  rw [hh]
  have hp (g : GeometricGWRecord) :
      ENNReal.ofReal (sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation g n)) =
        ((independentForestLaw ρ (geometricGWPopulation g n)).prod (independentBridgeLaw ℕ))
          (sourceTerminalListBridgeEvent t A γ b I z (geometricGWPopulation g n)) := by
    rw [← source_terminal_list_bridge_probability t A γ b I z
      (geometricGWPopulation g n) hα hcap hγ]
    exact ofReal_measureReal (measure_ne_top _ _)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun g ↦
      (source_terminal_mark_probability_mem t A γ b I z (geometricGWPopulation g n) hα hcap).1))
    (measurable_of_countable _).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro g
  exact (hp g).symm

end SRWTightness
