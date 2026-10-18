import SRWTightness.SourceSiteTiltApproximation
import SRWTightness.SourceGreenScaleComparison

open Filter
open scoped Topology

namespace SRWTightness

/-- The actual source CLT error preserves two-sided terminal bounds at scale 1/d. -/
theorem source_terminal_CLT_absorption (c C : ℝ) (hc : 0 < c) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ pG pT : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      c / d ≤ pG → pG ≤ C / d → |pT - pG| ≤ sourceSiteTiltError t →
      (c / 2) / d ≤ pT ∧ pT ≤ (C + c / 2) / d := by
  have herr : ∀ᶠ t : ℝ in atTop,
      sourceSiteTiltError t * sourceLowerTime (sourceLowerRadius t) < c / 2 :=
    sourceSiteTiltError_times_time_tendsto_zero.eventually (gt_mem_nhds (by linarith))
  have hall : ∀ᶠ t : ℝ in atTop, ∀ pG pT : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      c / d ≤ pG → pG ≤ C / d → |pT - pG| ≤ sourceSiteTiltError t →
      (c / 2) / d ≤ pT ∧ pT ≤ (C + c / 2) / d := by
    filter_upwards [herr, eventually_ge_atTop (sourceScaleThreshold 4)] with t he ht
    intro pG pT
    dsimp only
    intro hlo hup hdist
    have hd := sourceLowerTime_ge_one t ht
    have hd0 : 0 < sourceLowerTime (sourceLowerRadius t) := by linarith
    have herr' : sourceSiteTiltError t ≤ (c / 2) / sourceLowerTime (sourceLowerRadius t) :=
      (le_div_iff₀ hd0).mpr he.le
    obtain ⟨hl, hu⟩ := abs_le.mp hdist
    have hsplit : c / sourceLowerTime (sourceLowerRadius t) =
        2 * ((c / 2) / sourceLowerTime (sourceLowerRadius t)) := by ring
    constructor
    · linarith
    · rw [add_div]
      linarith
  exact eventually_atTop.1 hall

end SRWTightness
