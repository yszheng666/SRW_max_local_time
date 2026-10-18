import SRWTightness.SourcePairObservationIndex
import SRWTightness.TranslatedDiskGeometry

namespace SRWTightness

/-- A late pair lies in the first site's terminal observation disk. -/
theorem source_late_pair_mem_terminal_disk (A : ℝ) (I : ℕ) (b w : Site)
    (hA : 0 < A)
    (hcut : Real.sqrt (normSq (w - b)) ≤
      A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio)) :
    w ∈ translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)) := by
  have hB := diskEnergyGapRatio_gt_four
  have ha : 0 < A * diskEnergyGapRatio ^ I := mul_pos hA (pow_pos (by linarith) _)
  have hden : 1 < 8 * diskEnergyGapRatio := by linarith
  have hsmall : A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) <
      A * diskEnergyGapRatio ^ I := (div_lt_self ha hden)
  have hdist := lt_of_le_of_lt hcut hsmall
  have hs := Real.sq_sqrt (normSq_nonneg (w - b))
  have hn := Real.sqrt_nonneg (normSq (w - b))
  rw [mem_translateFinset_iff, mem_diskFinset]
  change normSq (w - b) < (A * diskEnergyGapRatio ^ I) ^ 2
  nlinarith

end SRWTightness
