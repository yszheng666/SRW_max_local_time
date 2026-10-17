import SRWTightness.TerminalListSamples
import SRWTightness.SourceTerminalContinuousEvent

open MeasureTheory

namespace SRWTightness

/-- Ordered terminal marks and finite samples give the same continuous bridge event probability. -/
theorem terminal_list_continuous_event_probability (D K : Finset Site) (α : ℝ)
    [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))]
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ)
    (t A : ℝ) (I : ℕ) (F : MarkSamples K k → Fin ((I + 1) + 1) → ℝ)
    (At q aStar d γ : ℝ) (hγ : 0 ≤ γ) :
    ((independentForestLaw (referenceMarkLaw D K α) k).prod
      (independentBridgeLaw ℕ)).real
      ((fun p ↦ (F (terminalListSamples 0 k p.1), p.2)) ⁻¹'
        sourceTerminalContinuousEvent t A I At q aStar d γ) =
    ((markProductLaw D K α k).prod (independentBridgeLaw ℕ)).real
      ((fun p ↦ (F p.1, p.2)) ⁻¹'
        sourceTerminalContinuousEvent t A I At q aStar d γ) := by
  rw [← source_terminal_continuous_preimage_probability
    (independentForestLaw (referenceMarkLaw D K α) k) t A I
    (fun rs ↦ F (terminalListSamples 0 k rs)) At q aStar d γ hγ,
    ← source_terminal_continuous_preimage_probability
      (markProductLaw D K α k) t A I F At q aStar d γ hγ]
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hlaw := terminalListSamples_product_law (referenceMarkLaw D K α)
    (independentBridgeLaw ℕ) (0 : Mark K) k
  have hs : MeasurableSet ((fun p : MarkSamples K k × (ℕ → GaussianCoefficientSpace) ↦
      (F p.1, p.2)) ⁻¹' sourceTerminalBridgeEvent t A I At q aStar d γ) :=
    (sourceTerminalBridgeEvent_measurable _ _ _ _ _ _ _ _).preimage
      (((measurable_of_countable F).comp measurable_fst).prodMk measurable_snd)
  have hh := congrArg (fun ρ ↦ ρ.real ((fun p ↦ (F p.1, p.2)) ⁻¹'
    sourceTerminalBridgeEvent t A I At q aStar d γ)) hlaw
  rw [measureReal_def, Measure.map_apply
    ((measurable_of_countable (terminalListSamples (0 : Mark K) k)).prodMap
      measurable_id) hs] at hh
  exact hh

end SRWTightness
