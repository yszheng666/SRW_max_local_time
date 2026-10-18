import SRWTightness.MarkedGWJointAuxiliary
import SRWTightness.SourceCoarseTerminalForestEvent

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The concrete reference forest/bridge success probability is exactly the previously estimated GW integral. -/
theorem source_coarse_terminal_reference_integral (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (n : ℕ)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    (hjoint : MarkedGWJointInput
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
    ((independentForestLaw μ 1).prod (independentBridgeLaw ℕ)).real
      (sourceCoarseTerminalForestEvent t A γ b I z n) =
        ∫ g in sourceGWCoarseBandEvent t n,
          sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation g n)
          ∂geometricGWRecordLaw 1 n := by
  dsimp only
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let ν := referenceMarkLaw D K α
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hh := markedGWJoint_auxiliary hjoint ν (independentBridgeLaw ℕ) n
    (sourceGWCoarseBandEvent t n)
    (fun g ↦ sourceTerminalListBridgeEvent t A γ b I z (geometricGWPopulation g n))
    (fun g ↦ sourceTerminalListBridgeEvent_measurable t A γ b I z (geometricGWPopulation g n))
    (sourceCoarseTerminalForestEvent_measurable t A γ b I z n)
  change ((independentForestLaw (finiteRecordReferenceMeasure ν n) 1).prod
    (independentBridgeLaw ℕ) (sourceCoarseTerminalForestEvent t A γ b I z n)).toReal = _
  change ((independentForestLaw (finiteRecordReferenceMeasure ν n) 1).prod
    (independentBridgeLaw ℕ) (sourceCoarseTerminalForestEvent t A γ b I z n)) = _ at hh
  rw [hh]
  have hp (g : GeometricGWRecord) :
      ENNReal.ofReal (sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation g n)) =
        ((independentForestLaw ν (geometricGWPopulation g n)).prod (independentBridgeLaw ℕ))
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
