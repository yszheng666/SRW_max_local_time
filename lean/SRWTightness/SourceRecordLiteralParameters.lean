import SRWTightness.SourceRootDepth
import SRWTightness.SourceExcursionDomains

namespace SRWTightness

/-- The actual nonnegative root depth is the manuscript's integer floor in its valid range. -/
theorem source_record_integer_depth (R m : ℝ) (hm : 0 < m) (hR : 32 * m ≤ R) :
    (sourceRootDepth R m : ℤ) = ⌊Real.log (R / (32 * m))⌋ := by
  unfold sourceRootDepth
  apply Int.natCast_floor_eq_floor
  apply Real.log_nonneg
  exact (one_le_div (by positivity)).mpr hR

/-- The actual record radii and buffer are exactly the manuscript's geometric parameters. -/
theorem source_record_literal_parameters (m r : ℝ) (ℓ j : ℕ) :
    sourceRecordRadius m ℓ j = m * Real.exp ((ℓ : ℝ) - (j : ℝ)) ∧
      sourceRecordBuffer r = 4 * r + 10 ∧
      sourceRecordRadius m ℓ ℓ = m := by
  simp [sourceRecordRadius, sourceRecordBuffer]

/-- The terminal generation runs between the original inner and outer buffered circles. -/
theorem source_record_terminal_domains (m r : ℝ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (b : Site) :
    sourceEntranceDomain m r ℓ b (ℓ - 1) =
      translateFinset b (diskFinset (m - (4 * r + 10))) ∧
    sourceExitDomain m r ℓ b (ℓ - 1) =
      translateFinset b (diskFinset (Real.exp 1 * m + (4 * r + 10))) := by
  have hi : ℓ - 1 + 1 = ℓ := by omega
  have ht : sourceRecordRadius m ℓ ℓ = m := by simp [sourceRecordRadius]
  have ho := sourceRecordRadius_successor m ℓ (ℓ - 1)
  rw [hi, ht] at ho
  constructor
  · simp only [sourceEntranceDomain, hi, ht, sourceRecordBuffer]
  · simp only [sourceExitDomain, ← ho, sourceRecordBuffer]

end SRWTightness
