import SRWTightness.SourceGWCoarseEvent

namespace SRWTightness

/-- The deficit read from a GW record recovers exactly the root of its integer terminal count. -/
theorem source_gw_terminal_count_identity (t : ℝ) (L : ℕ) (r : GeometricGWRecord) :
    let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
    sourceTerminalRoot t q = geometricGWHeight r L ∧
      sourceTerminalRoot t q ^ 2 / 2 = (geometricGWPopulation r L : ℝ) := by
  dsimp only
  have he : sourceTerminalRoot t
      (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L) =
      geometricGWHeight r L := by
    unfold sourceTerminalRoot
    ring
  refine ⟨he, ?_⟩
  rw [he]
  unfold geometricGWHeight
  rw [Real.sq_sqrt (by positivity)]
  ring

end SRWTightness
