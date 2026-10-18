import SRWTightness.SourceCommonPairRowTime
import SRWTightness.SourceCommonPairRadiusLower

namespace SRWTightness

/-- For the manuscript gap and allowed coarse levels, all geometric row-bound premises follow. -/
theorem source_common_pair_actual_row_time (t : ℝ) (b w : Site) (j : ℕ)
    (ht : 10 ≤ Real.log t)
    (hρ : 1 ≤ Real.sqrt (normSq (w - b)))
    (houter : Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hj : j + sourceCommonPairGap t =
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))))
    (hscale : 32 * sourceLowerRadius t ≤ Real.exp t)
    (hdepth : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) :
    |sourceCommonPairRowScale t b w j - (t - (j : ℝ) + (sourceCommonPairGap t : ℝ))| ≤
      2 * (diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2) +
        1 / (2 / Real.pi) + Real.log 32 + 3 := by
  have hm := sourceCommonPairInnerRadius_ge_seventy t j (by linarith)
    (by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 70)]) hdepth
  have hgap : (5 : ℝ) ≤ (sourceCommonPairGap t : ℝ) := by
    have hn : 5 ≤ sourceCommonPairGap t := by unfold sourceCommonPairGap; omega
    exact_mod_cast hn
  have hJ : Real.log 4 + 1 ≤ (sourceCommonPairGap t : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hr : 0 < Real.sqrt (normSq (w - b)) := by linarith
  have hs := (source_common_pair_log_separation t _ hr houter j (sourceCommonPairGap t) hj).1
  have hl : Real.log (4 * Real.sqrt (normSq (w - b))) ≤
      Real.log (sourceCommonPairInnerRadius t j) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hr.ne']
    linarith
  have hsep := (Real.log_le_log_iff (mul_pos (by norm_num : (0 : ℝ) < 4) hr)
    (sourceCommonPairInnerRadius_pos t j)).mp hl
  exact source_common_pair_row_time t b w j (sourceCommonPairGap t) hρ houter hj hscale
    (by linarith) hsep

end SRWTightness
