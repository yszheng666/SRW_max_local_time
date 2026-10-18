import SRWTightness.SourceGWWindowVariation
import SRWTightness.TerminalRightWindows

namespace SRWTightness

/-- The full coarse barrier restricted to the manuscript terminal deficit band. -/
def sourceGWCoarseBandEvent (t : ℝ) (L : ℕ) : Set GeometricGWRecord :=
  {r | (∀ j : ℕ, 0 < j → j ≤ L → geometricGWHeight r j ≤
      4 + sourceBarrierSlope t * j -
        (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) ∧
    sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L ∈
      Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
        (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))}

/-- Every complete inner height window lies inside the true deficit band. -/
theorem source_gw_inner_window_subset (t : ℝ) (L i : ℕ)
    (hi : i < ⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊) :
    sourceGWCoarseWindowEvent t L
      (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i + 1) ⊆
        sourceGWCoarseBandEvent t L := by
  intro r hr
  refine ⟨hr.1, ?_⟩
  apply (terminal_right_inner_window _ i hi).2
  have hh := hr.2
  unfold sourceTerminalRoot at hh
  have hq := terminal_deficit_window_orientation _ _ _ hh
  simpa only [add_sub_cancel_right] using hq

/-- Complete source windows are disjoint, including their shared endpoints. -/
theorem source_gw_inner_windows_disjoint (t : ℝ) (L i j : ℕ) (hij : i ≠ j) :
    Disjoint
      (sourceGWCoarseWindowEvent t L
        (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i + 1))
      (sourceGWCoarseWindowEvent t L
        (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) j + 1)) := by
  apply Set.disjoint_left.mpr
  intro r hi hj
  have hwi := hi.2
  have hwj := hj.2
  unfold sourceTerminalRoot at hwi hwj
  have hqi := terminal_deficit_window_orientation _ _ _ hwi
  have hqj := terminal_deficit_window_orientation _ _ _ hwj
  simp only [add_sub_cancel_right] at hqi hqj
  exact hij (terminal_right_inner_unique _ _ i j hqi hqj)

/-- Every source record in the terminal band belongs to a covering window with an allowed parameter. -/
theorem source_gw_outer_window_cover (t : ℝ) (L : ℕ) (r : GeometricGWRecord)
    (hr : r ∈ sourceGWCoarseBandEvent t L) :
    (∃ i ≤ ⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊,
      r ∈ sourceGWCoarseWindowEvent t L
        (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i)) ∨
    r ∈ sourceGWCoarseWindowEvent t L
      (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) := by
  obtain h | h := terminal_right_outer_cover _ _ hr.2
  · obtain ⟨i, hi, _, hq⟩ := h
    left
    refine ⟨i, hi, hr.1, ?_⟩
    unfold sourceTerminalRoot
    exact ⟨by linarith [hq.2], by linarith [hq.1]⟩
  · right
    refine ⟨hr.1, ?_⟩
    unfold sourceTerminalRoot
    exact ⟨by linarith [h.2.2], by linarith [h.2.1]⟩

end SRWTightness
