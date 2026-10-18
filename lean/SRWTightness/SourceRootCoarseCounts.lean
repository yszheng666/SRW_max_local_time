import SRWTightness.SourceRootTubeCounts
import SRWTightness.SourceGWCoarseEvent

open Filter

namespace SRWTightness

/-- The full manuscript coarse barrier bounds every finite-tree generation by 8t². -/
theorem source_coarse_root_population_cap :
    ∀ᶠ t : ℝ in atTop,
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      ∀ (M : Type*) (r : FiniteExcursionRecord M n),
        (∀ j : ℕ, 0 < j → j ≤ n →
          geometricGWHeight (finiteRecordPopulationList n r) j ≤
            4 + sourceBarrierSlope t * j -
              (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) →
        ∀ i ≤ n, (finiteRecordLevelPopulation n r i : ℝ) ≤ 8 * t ^ 2 := by
  filter_upwards [source_deficit_large_conditions, source_root_gw_horizon_large] with t ht hn
  dsimp only
  intro M r hr i hi
  let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hbeta := sourceBarrierSlope_bounds t ht.1 ht.2.1
  have hd := sourceLowerTime_ge_one t ht.1
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hgap := sourceTerminalRoot_gap t 0 ht.1 ht.2.1
  have hthetaN : sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) ≤ 2 * t := by
    dsimp [sourceTerminalRoot, sourceTerminalHeight] at hgap
    nlinarith [mul_nonneg hbeta.1 (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)]
  have hN : (n : ℝ) = (sourceCoarseGeneration t : ℝ) := hn.2
  have hT : (n : ℝ) ≤ sourceTotalTime t := by
    unfold sourceTotalTime
    rw [hN]
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
      rw [hN] at hline
      linarith
  rw [geometricGWHeight, finite_record_gw_population n r (n - i) (by omega),
    Nat.sub_sub_self hi] at hheight
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (finiteRecordLevelPopulation n r i : ℝ) by positivity)
  have hnon := Real.sqrt_nonneg (2 * (finiteRecordLevelPopulation n r i : ℝ))
  nlinarith

/-- Full source coarse events satisfy the vanishing comparison-error bound without count premises. -/
theorem source_coarse_root_error_bound (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop,
      let n := sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1
      ∀ a : ℝ, 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ (M : Type*) (r : FiniteExcursionRecord M n),
        (∀ j : ℕ, 0 < j → j ≤ n →
          geometricGWHeight (finiteRecordPopulationList n r) j ≤
            4 + sourceBarrierSlope t * j -
              (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) →
        finiteRecordError (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))
          (fun _ ↦ 2 * (W * (a + 1) / sourceLowerRadius t *
            Real.log (sourceLowerRadius t / a))) n r ≤ sourceForestQuadraticError B W 8 t := by
  filter_upwards [source_coarse_root_population_cap, eventually_ge_atTop (Real.exp 1)] with t ht hte
  dsimp only
  intro a ha hcut M r hr
  have hp := ht M r hr
  have hb := source_forest_quadratic_count_error B W 8 (sourceLowerRadius t) a t
    hB hW (by norm_num) (sourceLowerRadius_pos t) ha hte hcut _ [r] (by
      intro i hi
      simpa only [forestLevelPopulation, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] using hp i hi)
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    sourceForestQuadraticError] using hb


/-- A single actual root's GW population coordinates equal the manuscript forward segment counts. -/
theorem source_single_forest_gw_population {M : Type*} (m buffer : ℝ) (ℓ : ℕ)
    (hℓ : 0 < ℓ) (b : Site) (D : Finset Site) (x : Site)
    (F : Site → PathWord → M) (ω : Sample) (r : FiniteExcursionRecord M (ℓ - 1))
    (hr : killedChildRecords D (sourceEntranceDomain m buffer ℓ b 0)
      (sourceExitDomain m buffer ℓ b 0) x
      (actualFiniteWordRecord (sourceTreeEntrance m buffer ℓ b)
        (sourceTreeExit m buffer ℓ b) F (ℓ - 1)) ω = [r])
    (j : ℕ) (hj : j < ℓ) :
    geometricGWPopulation (finiteRecordPopulationList (ℓ - 1) r) j =
      sourceForwardRecordCount m buffer ℓ 0 j b D x ω := by
  have hp := source_forest_population m buffer ℓ 0 j (Nat.zero_le _) hj b D x F ω
  rw [hr] at hp
  simp only [forestLevelPopulation, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero] at hp
  rw [finite_record_gw_population (ℓ - 1) r j (by omega)]
  have hidx : ℓ - 1 - j = ℓ - (j + 1) := by omega
  rw [hidx]
  exact hp

end SRWTightness
