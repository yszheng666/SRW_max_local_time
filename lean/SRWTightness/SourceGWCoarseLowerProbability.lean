import SRWTightness.SourceGWCoarseEvent

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Lower probability bound transferred to the source's complete coarse-window event. -/
theorem source_gw_coarse_lower_probability (hGW : GWBarrierLowerInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let y := sourceTerminalRoot t q + 1 / 4
        c * gwBarrierPrefactor L (Real.sqrt 2) y 4 (sourceGWLowerEndpoint t) *
            min (Real.sqrt (Real.sqrt 2 / (y * L))) 1 ≤
          (geometricGWRecordLaw 1 L).real (sourceGWCoarseWindowEvent t L q) := by
  obtain ⟨c, hc, hh⟩ := source_gw_actual_lower_tube_probability hGW
  refine ⟨c, hc, ?_⟩
  filter_upwards [hh, source_gw_lower_tube_subset] with t ht hsub
  dsimp only
  intro q hql hqu
  exact (ht q hql hqu).trans (measureReal_mono (hsub q hql hqu))

end SRWTightness
