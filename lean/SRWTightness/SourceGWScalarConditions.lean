import SRWTightness.SourceGWActualLowerTubeProbability

open Filter
open scoped Topology

namespace SRWTightness

/-- Actual source scales meet the scalar-comparison range uniformly over all allowed deficits. -/
theorem source_gw_scalar_conditions :
    ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let u := sourceTerminalRoot t q
        (1 : ℝ) ≤ L ∧ 2 ≤ u ∧ u + 1 / 4 ≤ 4 * L ∧ (L : ℝ) / 2 ≤ u ∧
          0 ≤ q ∧ q / 2 ≤ sourceGWLowerEndpoint t - (u + 1 / 4) := by
  filter_upwards [source_gw_natural_generation, source_deficit_large_conditions,
    source_gw_lower_conditions, source_gw_endpoint_margins] with t hN ht hc hm
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hd := sourceLowerTime_ge_one t ht
  have hTerr := (abs_le.mp (sourceTotalTime_error t ht)).2
  unfold sourceTotalTime at hTerr
  dsimp only
  intro q hql hqu
  have hu := sourceTerminalRoot_bounds t q ht htE hdsmall hlog hql hqu
  have hc' := hc _ hN.1 q hql hqu
  have hm' := hm q hql hqu
  refine ⟨by exact_mod_cast hN.2, by linarith [hu.1], hc'.2.2.2.1, ?_,
    (Real.sqrt_nonneg _).trans hql, hm'.2.1⟩
  rw [hN.1]
  linarith [hu.1]

end SRWTightness
