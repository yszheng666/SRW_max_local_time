import SRWTightness.GrowingForestLiteralError
import SRWTightness.SourceReverseLevelSum
import SRWTightness.SourceSingleRootGeometry

open scoped BigOperators
namespace SRWTightness

/-- The general forest error in the manuscript's forward level indices, with arbitrary buffer. -/
theorem source_general_forest_error {M : Type*} (B W H m a : ℝ)
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hH : 0 ≤ H) (hm : 0 < m)
    (ha : 0 < a) (ham : a ≤ m) (ℓ k : ℕ) (hk : k < ℓ)
    (rs : List (FiniteExcursionRecord M (ℓ - (k + 1)))) :
    (rs.map (finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
      (fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) (ℓ - (k + 1)))).sum ≤
    (4 * B + 2 * W) * (∑ j ∈ Finset.Icc (k + 1) (ℓ - 1),
      ((forestLevelPopulation (ℓ - (k + 1)) rs (ℓ - j) : ℝ) +
        forestLevelPopulation (ℓ - (k + 1)) rs (ℓ - (j + 1))) *
        H / sourceRecordRadius m ℓ (j + 1)) +
    (4 * B + 2 * W) * forestLevelPopulation (ℓ - (k + 1)) rs 0 *
      (a + 1) / m * Real.log (m / a) := by
  have h := growing_forest_literal_error B W H m a hB hW hH hm ha ham
    (ℓ - (k + 1)) rs
  rw [source_reverse_level_sum ℓ k hk] at h
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hidx : ℓ - (j + 1) + 1 = ℓ - j := by omega
  rw [hidx, source_single_root_radius m ℓ j (by omega)]

end SRWTightness
