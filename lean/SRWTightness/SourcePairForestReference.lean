import SRWTightness.MarkedGWJointAuxiliary
import SRWTightness.SourcePairForestEvent

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The concrete reference pair forest/bridge probability is exactly the previously estimated GW integral. -/
theorem source_pair_forest_reference_integral (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (f : ℝ) (n : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
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
      (sourcePairForestEvent t A b I i z y f n) =
        ∫ g in sourceGWCoarseBandEvent t n,
          sourcePairMarkProbability t A b I i z y (geometricGWPopulation g n) f
          ∂geometricGWRecordLaw 1 n := by
  dsimp only
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let ν := referenceMarkLaw D K α
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hh := markedGWJoint_auxiliary hjoint ν (independentBridgeLaw ℕ) n
    (sourceGWCoarseBandEvent t n)
    (fun g ↦ sourcePairListEvent t A b I i z y (geometricGWPopulation g n) f)
    (fun g ↦ sourcePairListEvent_measurable t A b I i z y (geometricGWPopulation g n) f)
    (sourcePairForestEvent_measurable t A b I i z y f n)
  change ((independentForestLaw (finiteRecordReferenceMeasure ν n) 1).prod
    (independentBridgeLaw ℕ) (sourcePairForestEvent t A b I i z y f n)).toReal = _
  change ((independentForestLaw (finiteRecordReferenceMeasure ν n) 1).prod
    (independentBridgeLaw ℕ) (sourcePairForestEvent t A b I i z y f n)) = _ at hh
  rw [hh]
  have hp (g : GeometricGWRecord) :
      ENNReal.ofReal (sourcePairMarkProbability t A b I i z y (geometricGWPopulation g n) f) =
        ((independentForestLaw ν (geometricGWPopulation g n)).prod (independentBridgeLaw ℕ))
          (sourcePairListEvent t A b I i z y (geometricGWPopulation g n) f) := by
    rw [← source_pair_list_probability t A b I i hA ht hI z y
      (geometricGWPopulation g n) f hα hcap]
    exact ofReal_measureReal (measure_ne_top _ _)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun g ↦
      (source_pair_mark_probability_mem t A b I i z y (geometricGWPopulation g n) f hα hcap).1))
    (measurable_of_countable _).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro g
  exact (hp g).symm

end SRWTightness
