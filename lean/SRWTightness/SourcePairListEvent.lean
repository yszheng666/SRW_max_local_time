import SRWTightness.SourcePairMarkProbability
import SRWTightness.TerminalListSamples

open MeasureTheory

namespace SRWTightness

/-- The measurable pair-prefix event read from the ordered terminal leaf marks. -/
def sourcePairListEvent (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ) (f : ℝ) :
    Set (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) ×
      (ℕ → GaussianCoefficientSpace)) :=
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let u := Real.sqrt (2 * (k : ℝ))
  let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
  let F := fun Y j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
    (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y
  (fun p ↦ (F (terminalListSamples 0 k p.1), p.2)) ⁻¹'
    sourcePairUpperEvent t A I i (sourceTerminalThreshold t u) q f

theorem sourcePairListEvent_measurable (t A : ℝ) (b : Site) (I i : ℕ)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ) (f : ℝ)
    [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))] :
    MeasurableSet (sourcePairListEvent t A b I i z y k f) := by
  unfold sourcePairListEvent
  apply (sourcePairUpperEvent_measurable _ _ _ _ _ _ _).preimage
  have hF : Measurable (fun (rs : List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I))))) j ↦
    normalizedWeightedSum (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) k
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
      (Real.sqrt (2 * (k : ℝ)))
      (pairObservationWeight
        (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
        (sourcePairAverageFamily b A I i) z y j) (terminalListSamples 0 k rs)) :=
    measurable_of_countable _
  exact (hF.comp measurable_fst).prodMk measurable_snd

/-- Independent ordered leaf lists have exactly the original pair-reference probability. -/
theorem source_pair_list_probability (t A : ℝ) (b : Site) (I i : ℕ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ) (f : ℝ)
    [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ≤ 1) :
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    ((independentForestLaw (referenceMarkLaw D M α) k).prod (independentBridgeLaw ℕ)).real
      (sourcePairListEvent t A b I i z y k f) = sourcePairMarkProbability t A b I i z y k f := by
  dsimp only
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let u := Real.sqrt (2 * (k : ℝ))
  let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
  let μ := markProductLaw D M α k
  let σ := independentForestLaw (referenceMarkLaw D M α) k
  let F := fun Y j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
    (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y
  let E := sourcePairUpperEvent t A I i (sourceTerminalThreshold t u) q f
  letI := referenceMarkLaw_isProbabilityMeasure D M α hα hcap
  letI : IsProbabilityMeasure μ := markProductLaw_isProbabilityMeasure D M α hα hcap k
  have hF : Measurable F := measurable_of_countable _
  have hE : MeasurableSet E := sourcePairUpperEvent_measurable _ _ _ _ _ _ _
  have hlaw := terminalListSamples_product_law (referenceMarkLaw D M α)
    (independentBridgeLaw ℕ) (0 : Mark M) k
  have hh := congrArg (fun ρ ↦ ρ.real ((fun p ↦ (F p.1, p.2)) ⁻¹' E)) hlaw
  have hs : MeasurableSet ((fun p : MarkSamples M k × (ℕ → GaussianCoefficientSpace) ↦
      (F p.1, p.2)) ⁻¹' E) :=
    hE.preimage ((hF.comp measurable_fst).prodMk measurable_snd)
  rw [map_measureReal_apply ((measurable_of_countable (terminalListSamples (0 : Mark M) k)).prodMap
    measurable_id) hs] at hh
  have hm := Measure.map_prod_map μ (independentBridgeLaw ℕ) hF measurable_id
  rw [Measure.map_id] at hm
  have he := source_pair_original_probability b t A I i hA ht hI D M z y k α
    (2 / Real.pi) u (sourceTerminalThreshold t u) q f μ
  dsimp only at he
  rw [hm, map_measureReal_apply (hF.prodMap measurable_id) hE] at he
  exact hh.trans he.symm

end SRWTightness
