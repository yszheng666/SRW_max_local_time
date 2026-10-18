import SRWTightness.SourceRootCoarseCounts

open Filter
open scoped BigOperators

namespace SRWTightness

/-- The comparison error before substituting the observation cutoff. -/
theorem source_forest_quadratic_raw_error {M : Type*}
    (B W D m a t : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hm : 0 < m) (ha : 1 ≤ a) (ht : Real.exp 1 ≤ t) (hcut : a ≤ m / t ^ 6)
    (n : ℕ) (rs : List (FiniteExcursionRecord M n))
    (hcounts : ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ D * t ^ 2) :
    (rs.map (finiteRecordError (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
      (fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n)).sum ≤
        224 * B * D * t ^ 2 / m +
          2 * W * D * t ^ 2 * (a + 1) / m * Real.log (m / a) := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ht0 : 0 < t := by linarith
  have ham : a ≤ m := hcut.trans (div_le_self hm.le (one_le_pow₀ (by linarith : 1 ≤ t)))
  have hlog : 0 ≤ Real.log (m / a) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith : 0 < a)).mpr (by simpa using ham))
  have hb := forest_error_population_bound
    (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
    (2 * (W * (a + 1) / m * Real.log (m / a))) n rs (fun _ ↦ D * t ^ 2)
    (by intro i hi; dsimp [growingRecordRadius]; positivity) (by positivity) hcounts
  have hsum : (∑ i ∈ Finset.range n,
      (D * t ^ 2 + D * t ^ 2) * (4 * (B * 14 / growingRecordRadius m i))) ≤
      224 * B * D * t ^ 2 / m := by
    calc
      _ = (112 * B * D * t ^ 2) * ∑ i ∈ Finset.range n, 1 / growingRecordRadius m i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (112 * B * D * t ^ 2) * (2 / m) :=
        mul_le_mul_of_nonneg_left (growing_record_reciprocal_sum m hm n) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ 224 * B * D * t ^ 2 / m +
        (2 * (W * (a + 1) / m * Real.log (m / a))) * (D * t ^ 2) :=
      add_le_add hsum le_rfl
    _ = _ := by ring

/-- The first inequality of source (5.17), under its actual coarse barrier. -/
theorem source_coarse_root_raw_error_bound (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
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
            Real.log (sourceLowerRadius t / a))) n r ≤ 1792 * B * t ^ 2 / sourceLowerRadius t +
          16 * W * t ^ 2 * (a + 1) / sourceLowerRadius t *
            Real.log (sourceLowerRadius t / a) := by
  filter_upwards [source_coarse_root_population_cap, eventually_ge_atTop (Real.exp 1)] with t ht hte
  dsimp only
  intro a ha hcut M r hr
  have hp := ht M r hr
  have hb := source_forest_quadratic_raw_error B W 8 (sourceLowerRadius t) a t
    hB hW (by norm_num) (sourceLowerRadius_pos t) ha hte hcut _ [r] (by
      intro i hi
      simpa only [forestLevelPopulation, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero] using hp i hi)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hb
  convert hb using 1 <;> ring

end SRWTightness
