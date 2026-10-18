import SRWTightness.SourceRootDepth

namespace SRWTightness

/-- The manuscript floor depth is at most logarithmic outer time. -/
theorem source_root_depth_le_time (R m t : ℝ) (hm : 0 < m) (hscale : 32 * m ≤ R)
    (hmone : 1 ≤ 32 * m) (ht : R ≤ Real.exp t) :
    (sourceRootDepth R m : ℝ) ≤ t := by
  have hR : 0 < R := by linarith
  have hd : 0 < 32 * m := by positivity
  have hq : 1 ≤ R / (32 * m) := (one_le_div hd).mpr hscale
  have hqR : R / (32 * m) ≤ R := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hlo := Real.log_nonneg hq
  have hf := Nat.floor_le hlo
  have hl := Real.log_le_log (div_pos hR hd) hqR
  have hu := Real.log_le_log hR ht
  rw [Real.log_exp] at hu
  exact hf.trans (hl.trans hu)

end SRWTightness
