import SRWTightness.SourceForestApplicationGeometry
import SRWTightness.SourceGWActualLowerTubeProbability

open Filter

namespace SRWTightness

/-- The actual source root's internal depth equals the natural GW horizon, including truncation. -/
theorem source_root_gw_horizon (t : ℝ) :
    sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 =
      (sourceCoarseGeneration t).toNat := by
  have hh := sourceCoarseGeneration_at_radius (Real.exp t) (Real.exp_pos t)
  simp only [Real.log_exp] at hh
  rw [hh, sourceRootDepth, ← Int.floor_toNat]
  omega

/-- The actual root depth is eventually positive and has the real horizon used by GW estimates. -/
theorem source_root_gw_horizon_large :
    ∀ᶠ t : ℝ in atTop,
      0 < sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 ∧
      ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) =
        (sourceCoarseGeneration t : ℝ) := by
  filter_upwards [source_gw_natural_generation] with t ht
  rw [source_root_gw_horizon]
  exact ⟨ht.2, ht.1⟩

/-- The existing GW tube estimate holds at the actual excursion root's internal depth. -/
theorem source_root_gw_lower_tube_probability (hGW : GWBarrierLowerInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let y := sourceTerminalRoot t q + 1 / 4
        c * gwBarrierPrefactor n (Real.sqrt 2) y 4 (sourceGWLowerEndpoint t) *
            min (Real.sqrt (Real.sqrt 2 / (y * n))) 1 ≤
          (geometricGWRecordLaw 1 n).real (sourceGWLowerTubeEvent t n q) := by
  obtain ⟨c, hc, hh⟩ := source_gw_actual_lower_tube_probability hGW
  refine ⟨c, hc, ?_⟩
  filter_upwards [hh] with t ht
  simpa only [source_root_gw_horizon] using ht

end SRWTightness
