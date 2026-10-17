import SRWTightness.SourceCommonPairForestError
import SRWTightness.SourceCommonPrefixPopulationCap

open Filter
namespace SRWTightness

/-- The common coarse barrier itself makes the complete record-comparison error uniformly small. -/
theorem source_common_prefix_error_small
    (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (ρ : ℝ) (j : ℕ), 1 ≤ ρ →
      ρ ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (M : Type) (r : FiniteExcursionRecord M j),
      (∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceCommonPairInnerRadius t j) i))
        (fun _ ↦ 2 * (W * (2 * ρ + 1) / sourceCommonPairInnerRadius t j *
          Real.log (sourceCommonPairInnerRadius t j / (2 * ρ)))) j r < ε := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    (source_forest_quadratic_error_tendsto_zero B W 8).eventually (gt_mem_nhds hε),
    source_common_prefix_population_cap] with t ht he hp
  intro ρ j hρ ho hi hd M r hbar
  have hpop := hp j hd M r hbar
  have hh := source_common_pair_forest_error B W 8 t ρ j hB hW (by norm_num)
    ht hρ ho hi hd j [r] (by
      intro i hi
      simpa only [forestLevelPopulation, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] using hpop i hi)
  have hlt := hh.trans_lt he
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using hlt

end SRWTightness
