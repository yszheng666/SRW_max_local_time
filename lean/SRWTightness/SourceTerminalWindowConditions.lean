import SRWTightness.SourceTerminalThresholdAsymptotic
import SRWTightness.SourcePointEnergyTime

open Filter
open scoped Topology

namespace SRWTightness

/-- One time threshold controls the actual terminal window and center-variance errors uniformly. -/
theorem source_terminal_window_conditions (ε : ℝ) (hε : 0 < ε) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (q : ℝ),
      q ∈ Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
        (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) →
      |sourceTerminalThreshold t (sourceTerminalRoot t q) -
        (2 * sourceLowerTime (sourceLowerRadius t) + q)| ≤ ε ∧
      |sourcePointEnergyTime b (sourceLowerRadius t) 14 -
        sourceLowerTime (sourceLowerRadius t)| ≤
        sourcePointEnergyTimeError + sourceLowerTimeError := by
  have herr : ∀ᶠ t : ℝ in atTop, sourceTerminalThresholdError t < ε :=
    sourceTerminalThresholdError_tendsto_zero.eventually (gt_mem_nhds hε)
  have hall : ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (q : ℝ),
      q ∈ Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
        (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) →
      |sourceTerminalThreshold t (sourceTerminalRoot t q) -
        (2 * sourceLowerTime (sourceLowerRadius t) + q)| ≤ ε ∧
      |sourcePointEnergyTime b (sourceLowerRadius t) 14 -
        sourceLowerTime (sourceLowerRadius t)| ≤
        sourcePointEnergyTimeError + sourceLowerTimeError := by
    filter_upwards [herr, source_terminal_threshold_asymptotic.2,
      eventually_ge_atTop (sourceScaleThreshold 4)] with t he ht hs
    intro b q hq
    have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) hs).2.2.1
    exact ⟨(ht q hq.1 hq.2).trans he.le,
      sourcePointEnergyTime_lowerTime_bound b _ 14 (by linarith) (by norm_num)
        (by linarith)⟩
  exact eventually_atTop.1 hall

end SRWTightness
