import SRWTightness.GWTubePopulationCap
import SRWTightness.SourceRootGWHorizon
import SRWTightness.SourceForestErrorDecay

open Filter

namespace SRWTightness

/-- The concrete source lower tube bounds every actual finite-tree generation by 8t². -/
theorem source_root_tube_population_cap :
    ∀ᶠ t : ℝ in atTop,
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        ∀ (M : Type*) (r : FiniteExcursionRecord M n),
        finiteRecordPopulationList n r ∈ sourceGWLowerTubeEvent t n q →
        ∀ i ≤ n, (finiteRecordLevelPopulation n r i : ℝ) ≤ 8 * t ^ 2 := by
  filter_upwards [source_deficit_large_conditions, source_root_gw_horizon_large] with t ht hn
  dsimp only
  intro q hqlo hqhi M r hr i hi
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hterminal := sourceTerminalRoot_bounds t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hqlo hqhi
  have hbeta := sourceBarrierSlope_bounds t ht.1 ht.2.1
  have hd := sourceLowerTime_ge_one t ht.1
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hgap := sourceTerminalRoot_gap t 0 ht.1 ht.2.1
  have hthetaN : sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) ≤ 2 * t := by
    dsimp [sourceTerminalRoot, sourceTerminalHeight] at hgap
    nlinarith [mul_nonneg hbeta.1 (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)]
  have hend : sourceGWLowerEndpoint t ≤ 4 * t := by
    have hcurv := Real.rpow_nonneg
      (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith) (2 / 5 : ℝ)
    unfold sourceGWLowerEndpoint
    linarith
  exact finite_record_tube_population_cap _ hn.1 t _ _ _ _ _ _ _ _ ht2
    (by norm_num) (by linarith) hend (by linarith [hterminal.2]) r hr i hi

/-- Concrete source tube events satisfy the vanishing comparison-error bound without count premises. -/
theorem source_root_tube_error_bound (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop,
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      ∀ a : ℝ, 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        ∀ (M : Type*) (r : FiniteExcursionRecord M n),
        finiteRecordPopulationList n r ∈ sourceGWLowerTubeEvent t n q →
        finiteRecordError (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))
          (fun _ ↦ 2 * (W * (a + 1) / sourceLowerRadius t *
            Real.log (sourceLowerRadius t / a))) n r ≤ sourceForestQuadraticError B W 8 t := by
  filter_upwards [source_root_tube_population_cap, eventually_ge_atTop (Real.exp 1)] with t ht hte
  dsimp only
  intro a ha hcut q hqlo hqhi M r hr
  have hp := ht q hqlo hqhi M r hr
  have hb := source_forest_quadratic_count_error B W 8 (sourceLowerRadius t) a t
    hB hW (by norm_num) (sourceLowerRadius_pos t) ha hte hcut _ [r] (by
      intro i hi
      simpa only [forestLevelPopulation, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] using hp i hi)
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    sourceForestQuadraticError] using hb

end SRWTightness
