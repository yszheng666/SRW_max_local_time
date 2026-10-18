import SRWTightness.MarkedGWForestEvent
import SRWTightness.SourceTerminalListBridge
import SRWTightness.SourceContinuationProbability

open MeasureTheory
namespace SRWTightness

/-- The remaining forest succeeds through the shifted coarse band and original terminal bridge event.
The explicit zero-root exclusion matches the source convention p_nu(0)=0. -/
def sourceContinuationForestEvent (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ν n k : ℕ) :
    Set (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n) ×
      (ℕ → GaussianCoefficientSpace)) :=
  {p | k ≠ 0 ∧ forestPopulationList n p.1 ∈ sourceContinuationBand t ν n ∧
    (p.1.flatMap (finiteRecordLeaves n), p.2) ∈ sourceTerminalListBridgeEvent t A γ b I z
      (geometricGWPopulation (forestPopulationList n p.1) n)}

theorem sourceContinuationForestEvent_measurable (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (ν n k : ℕ)
    [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSingletonClass (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
    [MeasurableSpace (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord
      (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) n))] :
    MeasurableSet (sourceContinuationForestEvent t A γ b I z ν n k) := by
  by_cases hk : k = 0
  · simp [sourceContinuationForestEvent, hk]
  · simp only [sourceContinuationForestEvent, ne_eq, hk, not_false_eq_true, true_and]
    exact markedGWForestEvent_measurable n (sourceContinuationBand t ν n)
      (fun g ↦ sourceTerminalListBridgeEvent t A γ b I z (geometricGWPopulation g n))
      (fun g ↦ sourceTerminalListBridgeEvent_measurable t A γ b I z (geometricGWPopulation g n))

end SRWTightness
