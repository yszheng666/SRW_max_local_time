import SRWTightness.TerminalListSamples
import SRWTightness.SourceCoarseTerminalForestEvent

open scoped BigOperators

namespace SRWTightness

/-- Reading a list at its exact length preserves the sum of every visit coordinate. -/
theorem terminal_list_visit_sum (K : Finset Site) (rs : List (Mark K)) (k : ℕ)
    (hlen : rs.length = k) (y : K) :
    (∑ i : Fin k, (terminalListSamples 0 k rs i y : ℝ)) =
      (((rs.map (fun v ↦ v y)).sum : ℕ) : ℝ) := by
  subst k
  have he : List.ofFn (terminalListSamples (0 : Mark K) rs.length rs) = rs := by
    have hf : terminalListSamples (0 : Mark K) rs.length rs = rs.get := by
      funext i
      simp [terminalListSamples]
    rw [hf, List.ofFn_get]
  have hn : (∑ i : Fin rs.length, terminalListSamples 0 rs.length rs i y) =
      (rs.map (fun v ↦ v y)).sum := by
    have hh := congrArg (fun l : List (Mark K) ↦ (l.map (fun v ↦ v y)).sum) he
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hh
  exact_mod_cast hn

/-- The integer GW population used by the terminal event reads exactly all leaf visit coordinates. -/
theorem terminal_tree_visit_sum (K : Finset Site) (n : ℕ)
    (r : FiniteExcursionRecord (Mark K) n) (y : K) :
    let k := geometricGWPopulation (finiteRecordPopulationList n r) n
    (∑ i : Fin k, (terminalListSamples 0 k (finiteRecordLeaves n r) i y : ℝ)) =
      ((((finiteRecordLeaves n r).map (fun v ↦ v y)).sum : ℕ) : ℝ) := by
  exact terminal_list_visit_sum K _ _ (source_forest_terminal_sample_count n r) y

end SRWTightness
