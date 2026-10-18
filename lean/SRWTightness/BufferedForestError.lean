import SRWTightness.ForestPopulationError
import SRWTightness.GrowingRecordReciprocalSum

open scoped BigOperators

namespace SRWTightness

/-- Uniform buffers and quadratic generation caps bound the full finite forest error. -/
theorem buffered_forest_quadratic_error {M : Type*}
    (B W L H m a t : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hm : 0 < m) (ha : 0 < a) (ham : a ≤ m)
    (n : ℕ) (rs : List (FiniteExcursionRecord M n))
    (hcounts : ∀ i ≤ n, (forestLevelPopulation n rs i : ℝ) ≤ L * t ^ 2) :
    (rs.map (finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
      (fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n)).sum ≤
        16 * B * H * L * t ^ 2 / m +
          2 * W * L * t ^ 2 * (a + 1) / m * Real.log (m / a) := by
  have hlog : 0 ≤ Real.log (m / a) :=
    Real.log_nonneg ((le_div_iff₀ ha).mpr (by simpa using ham))
  have hb := forest_error_population_bound
    (fun i ↦ 4 * (B * H / growingRecordRadius m i))
    (2 * (W * (a + 1) / m * Real.log (m / a))) n rs (fun _ ↦ L * t ^ 2)
    (by intro i hi; dsimp [growingRecordRadius]; positivity) (by positivity) hcounts
  have hsum : (∑ i ∈ Finset.range n,
      (L * t ^ 2 + L * t ^ 2) * (4 * (B * H / growingRecordRadius m i))) ≤
      16 * B * H * L * t ^ 2 / m := by
    calc
      _ = (8 * B * H * L * t ^ 2) *
          ∑ i ∈ Finset.range n, 1 / growingRecordRadius m i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (8 * B * H * L * t ^ 2) * (2 / m) :=
        mul_le_mul_of_nonneg_left (growing_record_reciprocal_sum m hm n) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hb
    _ ≤ 16 * B * H * L * t ^ 2 / m +
        (2 * (W * (a + 1) / m * Real.log (m / a))) * (L * t ^ 2) :=
      add_le_add hsum le_rfl
    _ = _ := by ring

end SRWTightness
