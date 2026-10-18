import SRWTightness.SourceCommonPairDistance

namespace SRWTightness

/-- Every allowed inner coarse radius is at least the source terminal radius. -/
theorem sourceCommonPairInnerRadius_ge_lower (t : ℝ) (j : ℕ)
    (hj : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) :
    sourceLowerRadius t ≤ sourceCommonPairInnerRadius t j :=
  sourceRecordRadius_ge_terminal _ (sourceLowerRadius_pos t).le _ _ hj

/-- The lower source radius supplies the fixed size condition for common marks. -/
theorem sourceCommonPairInnerRadius_ge_seventy (t : ℝ) (j : ℕ)
    (ht : 1 ≤ Real.log t) (h70 : Real.log 70 ≤ 7 * Real.log t)
    (hj : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t)) :
    70 ≤ sourceCommonPairInnerRadius t j := by
  have hl : Real.log 70 ≤ Real.log (sourceLowerRadius t) := by
    rw [log_sourceLowerRadius]
    exact h70.trans (sourceLowerLogRadius_ge_seven_log t ht)
  exact ((Real.log_le_log_iff (by norm_num : (0 : ℝ) < 70)
    (sourceLowerRadius_pos t)).mp hl).trans (sourceCommonPairInnerRadius_ge_lower t j hj)

end SRWTightness
