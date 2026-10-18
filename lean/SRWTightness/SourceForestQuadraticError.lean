import SRWTightness.ForestPopulationError
import SRWTightness.GrowingRecordReciprocalSum
import SRWTightness.SourceTerminalErrorRate

open scoped BigOperators

namespace SRWTightness

/-- Quadratic population caps give the source comparison error rate, uniformly over the depth. -/
theorem source_forest_quadratic_count_error {M : Type*}
    (B W D m a t : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hm : 0 < m) (ha : 1 ≤ a) (ht : Real.exp 1 ≤ t) (hcut : a ≤ m / t ^ 6)
    (n : ℕ) (rs : List (FiniteExcursionRecord M n))
    (hcounts : ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ D * t ^ 2) :
    (rs.map (finiteRecordError (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
      (fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n)).sum ≤
        224 * B * D * t ^ 2 / m + 24 * W * D * Real.log t / t ^ 4 := by
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
  have hterm : (2 * (W * (a + 1) / m * Real.log (m / a))) * (D * t ^ 2) ≤
      24 * W * D * Real.log t / t ^ 4 := by
    calc
      _ ≤ (2 * (12 * W * Real.log t / t ^ 6)) * (D * t ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (source_terminal_error_rate W m a t hW hm ha ht hcut)
            (by norm_num)) (by positivity)
      _ = _ := by field_simp <;> ring
  exact hb.trans (add_le_add hsum hterm)

end SRWTightness
