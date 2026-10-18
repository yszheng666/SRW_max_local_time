import SRWTightness.SourceLongFineRecord
import SRWTightness.SourceForestQuadraticError

namespace SRWTightness

/-- Every fine-record error is nonnegative throughout the source observation range. -/
theorem source_long_fine_error_nonneg (B W t a : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W)
    (ht : 1 ≤ t) (ha : 1 ≤ a) (hcut : a ≤ sourceLowerRadius t / t ^ 6)
    (K : Finset Site) (ν : ℕ)
    (r : FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) :
    0 ≤ sourceLongFineError B W t a K ν r := by
  have hm := sourceLowerRadius_pos t
  have ham : a ≤ sourceLowerRadius t :=
    hcut.trans (div_le_self hm.le (one_le_pow₀ ht))
  have hlog : 0 ≤ Real.log (sourceLowerRadius t / a) :=
    Real.log_nonneg ((le_div_iff₀ (by linarith : 0 < a)).mpr (by simpa using ham))
  unfold sourceLongFineError
  rw [finiteRecordError_population_sum, finiteRecordTerminalError_constant]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    dsimp [growingRecordRadius]
    positivity
  · positivity

end SRWTightness
