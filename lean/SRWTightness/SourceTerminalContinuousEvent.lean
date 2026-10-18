import SRWTightness.SourceTerminalBridgeEvent

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The terminal windows and the continuous path barrier as stated in manuscript (5.10). -/
def sourceTerminalContinuousEvent (t A : ℝ) (I : ℕ) (At q aStar d γ : ℝ) :
    Set ((Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | At ≤ p.1 (Fin.last (I + 1)) ∧ p.1 (Fin.last (I + 1)) ≤ At + 1 ∧
    q - aStar - 1 ≤ p.1 ⟨I, by omega⟩ - 2 * sourceObservationTime t A I (I + 1) ∧
    p.1 ⟨I, by omega⟩ - 2 * sourceObservationTime t A I (I + 1) ≤ q - aStar ∧
    ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I + 1) →
      sourceBridgedPath t A I p.1 p.2 v ≤ q - (d - v) ^ γ}

/-- Dyadic and continuous terminal events have identical probabilities on the original product space. -/
theorem source_terminal_continuous_preimage_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (t A : ℝ) (I : ℕ) (F : Ω → Fin ((I + 1) + 1) → ℝ)
    (At q aStar d γ : ℝ) (hγ : 0 ≤ γ) :
    (μ.prod (independentBridgeLaw ℕ)).real
      ((fun p ↦ (F p.1, p.2)) ⁻¹' sourceTerminalBridgeEvent t A I At q aStar d γ) =
    (μ.prod (independentBridgeLaw ℕ)).real
      ((fun p ↦ (F p.1, p.2)) ⁻¹' sourceTerminalContinuousEvent t A I At q aStar d γ) := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hh := (Measure.quasiMeasurePreserving_snd
    (μ := μ) (ν := independentBridgeLaw ℕ)).ae
      (sourceTerminalBridgeEvent_ae_iff t A I At q aStar d γ hγ)
  filter_upwards [hh] with p hp
  exact propext (hp (F p.1))

end SRWTightness
