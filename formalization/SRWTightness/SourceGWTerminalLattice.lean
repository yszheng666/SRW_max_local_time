import SRWTightness.GWPositiveLattice
import SRWTightness.SourceDeficitBand

open Filter
open scoped Topology

namespace SRWTightness

/-- The actual source terminal band satisfies the lower GW input's endpoint lattice condition. -/
theorem source_gw_terminal_lattice :
    ∀ᶠ t : ℝ in atTop, ∀ q : ℝ,
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
      let u := sourceTerminalRoot t q
      gwPositiveLatticeIntersects (u + 1 / 4) (u + 3 / 4) ∧
        Set.Icc (u + 1 / 4) (u + 3 / 4) ⊆ Set.Ico u (u + 1) := by
  filter_upwards [source_deficit_large_conditions] with t ht
  obtain ⟨ht, htE, hd, hl⟩ := ht
  intro q hql hqu
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hu := (sourceTerminalRoot_bounds t q ht htE hd hl hql hqu).1
  exact ⟨gw_terminal_subwindow_lattice _ (by linarith), gw_terminal_subwindow_subset _⟩

end SRWTightness
