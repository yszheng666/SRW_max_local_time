import SRWTightness.ForestPopulationError
import SRWTightness.GrowingRecordDomains

open scoped BigOperators
namespace SRWTightness

/-- The full forest error has the literal adjacent-generation form for every admissible buffer. -/
theorem growing_forest_literal_error {M : Type*} (B W H m a : ℝ)
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hH : 0 ≤ H) (hm : 0 < m)
    (ha : 0 < a) (ham : a ≤ m) (n : ℕ) (rs : List (FiniteExcursionRecord M n)) :
    (rs.map (finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
      (fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n)).sum ≤
    (4 * B + 2 * W) * (∑ i ∈ Finset.range n,
      ((forestLevelPopulation n rs (i + 1) : ℝ) + forestLevelPopulation n rs i) *
        H / growingRecordRadius m i) +
    (4 * B + 2 * W) * forestLevelPopulation n rs 0 *
      (a + 1) / m * Real.log (m / a) := by
  have hlog : 0 ≤ Real.log (m / a) :=
    Real.log_nonneg ((one_le_div ha).mpr ham)
  rw [forest_error_population_sum, Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    have hp : 0 ≤ ((forestLevelPopulation n rs (i + 1) : ℝ) +
        forestLevelPopulation n rs i) * H / growingRecordRadius m i := by
      unfold growingRecordRadius
      positivity
    have h := mul_le_mul_of_nonneg_right
      (show 4 * B ≤ 4 * B + 2 * W by linarith) hp
    convert h using 1 <;> ring
  · have hp : 0 ≤ (forestLevelPopulation n rs 0 : ℝ) *
        (a + 1) / m * Real.log (m / a) := by positivity
    have h := mul_le_mul_of_nonneg_right
      (show 2 * W ≤ 4 * B + 2 * W by linarith) hp
    convert h using 1 <;> ring

end SRWTightness
