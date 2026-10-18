import SRWTightness.SourceWalkSuccessEvent

open MeasureTheory

namespace SRWTightness

/-- Countably many terminal populations share a single full-measure bridge set. -/
theorem source_walk_bridge_continuous_ae (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (hγ : 0 ≤ γ) :
    sourceLocalTimeBridgeSuccessEvent t A γ b I z =ᵐ[pathLaw.prod (independentBridgeLaw ℕ)]
      sourceLocalTimeSuccessEvent t A γ b I z := by
  have hk (k : ℕ) := sourceTerminalBridgeEvent_ae_iff t A I
    (sourceTerminalThreshold t (Real.sqrt (2 * (k : ℝ))))
    (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - Real.sqrt (2 * (k : ℝ)))
    (Real.sqrt (sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I + 1)))
    (sourceLowerTime (sourceLowerRadius t)) γ hγ
  have hall := (ae_all_iff.mpr hk)
  have hh := (Measure.quasiMeasurePreserving_snd
    (μ := pathLaw) (ν := independentBridgeLaw ℕ)).ae hall
  filter_upwards [hh] with p hp
  apply propext
  change (p ∈ sourceLocalTimeBridgeSuccessEvent t A γ b I z) ↔
    (p ∈ sourceLocalTimeSuccessEvent t A γ b I z)
  simp only [sourceLocalTimeBridgeSuccessEvent, sourceLocalTimeSuccessEvent, Set.mem_setOf_eq]
  rw [hp (sourceActualCount t b
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) p.1)]
  rfl

/-- The original local-time success event has the same probability with continuous bridges. -/
theorem source_walk_bridge_continuous_probability (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (hγ : 0 ≤ γ) :
    (pathLaw.prod (independentBridgeLaw ℕ)).real
      (sourceLocalTimeBridgeSuccessEvent t A γ b I z) =
    (pathLaw.prod (independentBridgeLaw ℕ)).real
      (sourceLocalTimeSuccessEvent t A γ b I z) := by
  apply congrArg ENNReal.toReal
  exact measure_congr (source_walk_bridge_continuous_ae t A γ b I z hγ)

end SRWTightness
