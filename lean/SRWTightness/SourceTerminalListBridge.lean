import SRWTightness.SourceTerminalListEvent

open MeasureTheory

namespace SRWTightness

/-- The source measurable terminal bridge event expressed directly in the ordered leaf marks. -/
def sourceTerminalListBridgeEvent (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ) :
    Set (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) ×
      (ℕ → GaussianCoefficientSpace)) :=
  let d := sourceLowerTime (sourceLowerRadius t)
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let u := Real.sqrt (2 * (k : ℝ))
  let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
  let F := fun i : Fin ((I + 1) + 1) ↦
    normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
      z k α (2 / Real.pi) u (diskObservationIndex (I + 1) i)
  let H := d - sourceObservationTime t A I (I + 1)
  let E := sourceTerminalBridgeEvent t A I (sourceTerminalThreshold t u)
    q (Real.sqrt H) d γ
  ((fun p ↦ ((fun i ↦ F i (terminalListSamples 0 k p.1)), p.2)) ⁻¹' E)

/-- The actual list-valued terminal bridge event is measurable. -/
theorem sourceTerminalListBridgeEvent_measurable (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))] :
    MeasurableSet (sourceTerminalListBridgeEvent t A γ b I z k) := by
  unfold sourceTerminalListBridgeEvent
  apply (sourceTerminalBridgeEvent_measurable _ _ _ _ _ _ _ _).preimage
  exact ((measurable_of_countable (fun (rs : List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) )
      (i : Fin ((I + 1) + 1)) ↦ normalizedObservation
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
      (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
      (Real.sqrt (2 * (k : ℝ))) (diskObservationIndex (I + 1) i)
      (terminalListSamples 0 k rs))).comp measurable_fst).prodMk measurable_snd

/-- The measurable and continuous source list events have equal probability for every mark-list law. -/
theorem source_terminal_list_bridge_continuous (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    (μ : Measure (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))))
    (hγ : 0 ≤ γ) :
    (μ.prod (independentBridgeLaw ℕ)).real (sourceTerminalListBridgeEvent t A γ b I z k) =
      (μ.prod (independentBridgeLaw ℕ)).real (sourceTerminalListEvent t A γ b I z k) := by
  unfold sourceTerminalListBridgeEvent sourceTerminalListEvent
  exact source_terminal_continuous_preimage_probability μ t A I
    (fun rs i ↦ normalizedObservation
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
      (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
      (Real.sqrt (2 * (k : ℝ))) (diskObservationIndex (I + 1) i)
      (terminalListSamples 0 k rs))
    (sourceTerminalThreshold t (Real.sqrt (2 * (k : ℝ))))
    (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - Real.sqrt (2 * (k : ℝ)))
    (Real.sqrt (sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I + 1)))
    (sourceLowerTime (sourceLowerRadius t)) γ hγ

/-- The source terminal probability already estimated is the actual independent-list/bridge probability. -/
theorem source_terminal_list_bridge_probability (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ≤ 1)
    (hγ : 0 ≤ γ) :
    let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
    let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    ((independentForestLaw (referenceMarkLaw D K α) k).prod
      (independentBridgeLaw ℕ)).real (sourceTerminalListBridgeEvent t A γ b I z k) =
        sourceTerminalMarkProbability t A γ b I z k := by
  dsimp only
  rw [source_terminal_list_bridge_continuous t A γ b I z k _ hγ]
  exact source_terminal_list_probability t A γ b I z k hα hcap hγ

end SRWTightness
