import SRWTightness.TerminalWindowVariation
import SRWTightness.SourceGWCoarseEvent

namespace SRWTightness

/-- Window variation at the actual terminal population of a source GW record. -/
theorem source_gw_terminal_weight_window (t : ℝ) (L : ℕ) (q : ℝ)
    (r : GeometricGWRecord) (hd : 0 < sourceLowerTime (sourceLowerRadius t))
    (hr : r ∈ sourceGWCoarseWindowEvent t L q) :
    let d := sourceLowerTime (sourceLowerRadius t)
    let q' := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
    Real.exp (-2 * d - 2 * q) / d ≤ Real.exp (-2 * d - 2 * q') / d ∧
      Real.exp (-2 * d - 2 * q') / d ≤
        Real.exp 2 * (Real.exp (-2 * d - 2 * q) / d) := by
  have hh := hr.2
  unfold sourceTerminalRoot at hh
  exact terminal_probability_weight_window _ _ _ hd
    (terminal_deficit_window_orientation _ _ _ hh)

end SRWTightness
