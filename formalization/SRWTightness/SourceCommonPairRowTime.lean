import SRWTightness.SourceCommonPairLogTime
import SRWTightness.SourceCommonPairRowLogBound

namespace SRWTightness

/-- An explicit uniform version of the manuscript common discrete-row scale estimate. -/
theorem source_common_pair_row_time (t : ℝ) (b w : Site) (j J : ℕ)
    (hρ : 1 ≤ Real.sqrt (normSq (w - b)))
    (houter : Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (hj : j + J = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))))
    (hscale : 32 * sourceLowerRadius t ≤ Real.exp t)
    (hm : 14 ≤ sourceCommonPairInnerRadius t j)
    (hsep : 4 * Real.sqrt (normSq (w - b)) ≤ sourceCommonPairInnerRadius t j) :
    |sourceCommonPairRowScale t b w j - (t - (j : ℝ) + (J : ℝ))| ≤
      2 * (diskGreenEnergyConstant / (2 / Real.pi) + Real.log 2) +
        1 / (2 / Real.pi) + Real.log 32 + 3 := by
  have hr := abs_le.mp (source_common_pair_row_log_bound t b w j hρ hsep)
  have ht := source_common_pair_killing_log_time t j hscale hm
  have hb := source_common_pair_buffer_log t j hm
  have hd := source_common_pair_log_separation t _ (by linarith) houter j J hj
  have hc : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  apply abs_le.mpr
  constructor <;> linarith [hr.1, hr.2, ht.1, ht.2, hb.1, hb.2, hd.1, hd.2]

end SRWTightness
