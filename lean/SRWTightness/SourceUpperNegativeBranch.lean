import SRWTightness.SourceUpperSlopeError

namespace SRWTightness

/-- The exact rounded source cutoff alone forces a t-scale negative-branch height. -/
theorem source_upper_negative_branch_square (t s α : ℝ) (k : ℕ) (ht : 0 < t)
    (hs : 0 ≤ s) (hslog : s ≤ Real.log t) :
    (2 / Real.pi) * t ^ 2 ≤
      (Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ)) +
        Real.sqrt (2 * ((k : ℝ) * α))) ^ 2 := by
  have hy := (source_upper_height_bounds t s ht hs hslog).1
  have hg : 0 ≤ (2 / Real.pi : ℝ) := by positivity
  have hc := Nat.le_ceil (sourceUpperHeight t s ^ 2 / Real.pi)
  have hcount : (2 / Real.pi) * t ^ 2 ≤ 2 * (sourceUpperVisitCutoff t s : ℝ) := by
    calc
      _ ≤ (2 / Real.pi) * sourceUpperHeight t s ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) hg
      _ = 2 * (sourceUpperHeight t s ^ 2 / Real.pi) := by ring
      _ ≤ 2 * (sourceUpperVisitCutoff t s : ℝ) :=
        mul_le_mul_of_nonneg_left hc (by norm_num)
  have ha := Real.sq_sqrt (show 0 ≤ 2 * (sourceUpperVisitCutoff t s : ℝ) by positivity)
  have hcross := mul_nonneg (Real.sqrt_nonneg (2 * (sourceUpperVisitCutoff t s : ℝ)))
    (Real.sqrt_nonneg (2 * ((k : ℝ) * α)))
  nlinarith [sq_nonneg (Real.sqrt (2 * ((k : ℝ) * α)))]

/-- The actual negative Gaussian branch has the source exp(-c*t²/d) decay. -/
theorem source_upper_negative_branch_exponential (t s α V d : ℝ) (k : ℕ)
    (ht : 0 < t) (hs : 0 ≤ s) (hslog : s ≤ Real.log t) (hV : 0 < V) (hd : 0 < d) :
    Real.exp (-(Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ)) +
      Real.sqrt (2 * ((k : ℝ) * α))) ^ 2 / (2 * (V * d))) ≤
    Real.exp (-((2 / Real.pi) / (2 * V)) * t ^ 2 / d) := by
  apply Real.exp_le_exp.mpr
  have hb := div_le_div_of_nonneg_right
    (neg_le_neg (source_upper_negative_branch_square t s α k ht hs hslog))
    (show 0 ≤ 2 * (V * d) by positivity)
  calc
    _ ≤ -((2 / Real.pi) * t ^ 2) / (2 * (V * d)) := hb
    _ = _ := by ring

end SRWTightness
