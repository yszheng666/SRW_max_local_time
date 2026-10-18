import SRWTightness.SourceRootCoarseCounts

open Filter
namespace SRWTightness

/-- Every admissible truncated common prefix inherits the manuscript quadratic population cap. -/
theorem source_common_prefix_population_cap :
    ∀ᶠ t : ℝ in atTop,
      ∀ (n : ℕ), n + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (M : Type*) (r : FiniteExcursionRecord M n),
        (∀ j : ℕ, 0 < j → j ≤ n →
          geometricGWHeight (finiteRecordPopulationList n r) j ≤
            4 + sourceBarrierSlope t * j -
              (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) →
        ∀ i ≤ n, (finiteRecordLevelPopulation n r i : ℝ) ≤ 8 * t ^ 2 := by
  filter_upwards [source_deficit_large_conditions, source_root_gw_horizon_large] with t ht hn
  intro n hdepth M r hr i hi
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hbeta := sourceBarrierSlope_bounds t ht.1 ht.2.1
  have hd := sourceLowerTime_ge_one t ht.1
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hgap := sourceTerminalRoot_gap t 0 ht.1 ht.2.1
  have hthetaN : sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) ≤ 2 * t := by
    dsimp [sourceTerminalRoot, sourceTerminalHeight] at hgap
    nlinarith [mul_nonneg hbeta.1 (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)]
  have hN : (n : ℝ) ≤ (sourceCoarseGeneration t : ℝ) := by
    have hnat : n ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by omega
    have hreal : (n : ℝ) ≤
        ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans_eq hn.2
  have hT : (n : ℝ) ≤ sourceTotalTime t := by
    unfold sourceTotalTime
    linarith
  have hheight : geometricGWHeight (finiteRecordPopulationList n r) (n - i) ≤ 4 * t := by
    by_cases hj0 : n - i = 0
    · rw [hj0, geometricGWHeight, finite_record_gw_population n r 0 (Nat.zero_le _),
        Nat.sub_zero, finiteRecordLevelPopulation_root]
      have hs : Real.sqrt 2 ≤ 2 := by norm_num
      norm_num only [Nat.cast_one, mul_one]
      linarith
    · have hj : n - i ≤ n := by omega
      have hjR : ((n - i : ℕ) : ℝ) ≤ n := by exact_mod_cast hj
      have hcurv := Real.rpow_nonneg
        (le_min (Nat.cast_nonneg (n - i)) (sub_nonneg.mpr (hjR.trans hT))) (2 / 5 : ℝ)
      have hh := hr (n - i) (by omega) hj
      have hline := mul_le_mul_of_nonneg_left hjR hbeta.1
      have hnline := mul_le_mul_of_nonneg_left hN hbeta.1
      linarith
  rw [geometricGWHeight, finite_record_gw_population n r (n - i) (by omega),
    Nat.sub_sub_self hi] at hheight
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (finiteRecordLevelPopulation n r i : ℝ) by positivity)
  have hnon := Real.sqrt_nonneg (2 * (finiteRecordLevelPopulation n r i : ℝ))
  nlinarith


end SRWTightness
