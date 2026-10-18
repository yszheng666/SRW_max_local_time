import SRWTightness.TerminalWindowSum

open Filter
open scoped Topology

namespace SRWTightness

/-- The actual source time eventually exceeds every fixed lower threshold. -/
theorem source_lower_time_eventually_ge (D : ℝ) :
    ∀ᶠ t : ℝ in atTop, D ≤ sourceLowerTime (sourceLowerRadius t) := by
  filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4),
    eventually_ge_atTop (Real.exp (D + sourceLowerTimeError))] with t ht htexp
  have htpos : 0 < t := (Real.exp_pos _).trans_le htexp
  have hlogt := Real.log_le_log (Real.exp_pos _) htexp
  rw [Real.log_exp] at hlogt
  have hlogm := Real.log_le_log htpos (sourceLowerRadius_ge_self t ht)
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  have hd := (abs_le.mp (sourceLowerTime_log_bound (sourceLowerRadius t)
    (by linarith))).1
  linarith

/-- Manuscript (7.27), bracketed by complete and covering unit-window sums. -/
theorem source_terminal_window_sum :
    ∀ᶠ t : ℝ in atTop,
      let d := sourceLowerTime (sourceLowerRadius t)
      (1 / 2 : ℝ) ≤ terminalInnerWindowWeight d / d ∧
        terminalInnerWindowWeight d / d ≤ terminalOuterWindowWeight d / d ∧
        terminalOuterWindowWeight d / d ≤ 6 := by
  filter_upwards [source_lower_time_eventually_ge 4] with t ht
  exact terminal_window_weight_normalized _ ht

end SRWTightness
