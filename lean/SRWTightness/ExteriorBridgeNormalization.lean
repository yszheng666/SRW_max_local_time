import SRWTightness.ExteriorWordLengths
import SRWTightness.ExternalExteriorBridge

namespace SRWTightness

/-- The retained cylinder weight times the exit probabilities of all deleted slots. -/
noncomputable def exteriorBridgeNormalization (C : Finset Site) (h : ExteriorPathRecord) : ℝ :=
  (1 / 4 : ℝ) ^ exteriorWordLength h *
    (h.1.map (fun slot ↦ traceExitProbability C slot.2.2.1 slot.2.2.2)).prod

/-- Reachable exits make the retained normalization strictly positive. -/
theorem exteriorBridgeNormalization_pos (C : Finset Site) (h : ExteriorPathRecord)
    (he : ∀ slot ∈ h.1, 0 < traceExitProbability C slot.2.2.1 slot.2.2.2) :
    0 < exteriorBridgeNormalization C h := by
  apply mul_pos (by positivity)
  apply List.prod_pos
  intro q hq
  obtain ⟨slot, hs, rfl⟩ := List.mem_map.mp hq
  exact he slot hs

end SRWTightness
