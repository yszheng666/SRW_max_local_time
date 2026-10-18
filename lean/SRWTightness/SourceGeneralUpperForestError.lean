import SRWTightness.SourceGeneralForestError

open scoped BigOperators
namespace SRWTightness

/-- The upper-only forest comparison has the literal source error without a smallness premise. -/
theorem source_general_upper_forest_error {M : Type*} (B W H m a : ℝ)
    (hB : 0 ≤ B) (hW : 0 ≤ W) (hH : 0 ≤ H) (hm : 0 < m)
    (ha : 0 < a) (ham : a ≤ m) (ℓ k : ℕ) (hk : k < ℓ)
    (rs : List (FiniteExcursionRecord M (ℓ - (k + 1)))) :
    (rs.map (finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
      (fun _ ↦ W * (a + 1) / m * Real.log (m / a)) (ℓ - (k + 1)))).sum ≤
    (4 * B + W) * (∑ j ∈ Finset.Icc (k + 1) (ℓ - 1),
      ((forestLevelPopulation (ℓ - (k + 1)) rs (ℓ - j) : ℝ) +
        forestLevelPopulation (ℓ - (k + 1)) rs (ℓ - (j + 1))) *
        H / sourceRecordRadius m ℓ (j + 1)) +
    (4 * B + W) * forestLevelPopulation (ℓ - (k + 1)) rs 0 *
      (a + 1) / m * Real.log (m / a) := by
  have h := source_general_forest_error (M := M) B (W / 2) H m a hB
    (by positivity) hH hm ha ham ℓ k hk rs
  have he : (fun _ : M ↦ 2 * ((W / 2) * (a + 1) / m * Real.log (m / a))) =
      (fun _ : M ↦ W * (a + 1) / m * Real.log (m / a)) := by
    funext x
    ring
  have hc : 4 * B + 2 * (W / 2) = 4 * B + W := by ring
  rw [he, hc] at h
  exact h

end SRWTightness
