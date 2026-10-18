import SRWTightness.SourceTerminalBridgeEvent
import SRWTightness.SourceSiteTiltApproximation

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The terminal event probability under observed coordinates equals its sample-space preimage. -/
theorem terminal_observation_preimage_probability {M : Finset Site} {k : ℕ}
    (μ : Measure (MarkSamples M k)) [SFinite μ]
    (t A : ℝ) (I : ℕ) (F : MarkSamples M k → Fin ((I + 1) + 1) → ℝ)
    (At q aStar d γ : ℝ) :
    ((μ.map F).prod (independentBridgeLaw ℕ)).real
      (sourceTerminalBridgeEvent t A I At q aStar d γ) =
    (μ.prod (independentBridgeLaw ℕ)).real
      ((fun p ↦ (F p.1, p.2)) ⁻¹' sourceTerminalBridgeEvent t A I At q aStar d γ) := by
  have hF : Measurable F := measurable_of_countable _
  have hh := Measure.map_prod_map μ (independentBridgeLaw ℕ) hF measurable_id
  rw [Measure.map_id] at hh
  rw [hh, map_measureReal_apply (hF.prodMap measurable_id)
    (sourceTerminalBridgeEvent_measurable _ _ _ _ _ _ _ _)]
  rfl

/-- The terminal preimage retains the exact normalized center-coordinate unit window. -/
theorem terminal_observation_preimage_window {I : ℕ} (t A At q aStar d γ : ℝ)
    (D M : Finset Site) (K : Fin (I + 1) → Finset Site) (z : M)
    (k : ℕ) (α g u : ℝ) (p : MarkSamples M k × (ℕ → GaussianCoefficientSpace))
    (hp : ((fun i ↦ normalizedObservation D M K z k α g u
      (diskObservationIndex (I + 1) i) p.1), p.2) ∈
      sourceTerminalBridgeEvent t A I At q aStar d γ) :
    At ≤ normalizedMarkSum M k α g u z p.1 ∧
      normalizedMarkSum M k α g u z p.1 ≤ At + 1 := by
  have hh := And.intro hp.1 hp.2.1
  simpa only [diskObservationIndex_last, normalizedObservation] using hh

end SRWTightness
