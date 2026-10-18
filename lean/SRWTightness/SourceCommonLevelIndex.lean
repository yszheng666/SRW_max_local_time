import SRWTightness.SourceCommonPairDistance

namespace SRWTightness

/-- At every positive common level, natural subtraction is exactly the manuscript index equation. -/
theorem sourceCommonPairLevel_eq_iff (t ρ : ℝ) (j : ℕ) (hj : 0 < j) :
    sourceCommonPairLevel t ρ = j ↔
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ := by
  unfold sourceCommonPairLevel
  omega

end SRWTightness
