import SRWTightness.SourceCommonPairParameters
import SRWTightness.SourceCoarseTime
import SRWTightness.TwoSiteOptimizedTilt

namespace SRWTightness

/-- The largest endpoint allowed by the manuscript common coarse barrier. -/
noncomputable def sourceCommonPairEndpoint (t : ℝ) (j : ℕ) : ℝ :=
  4 + sourceBarrierSlope t * j - (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)

/-- The intensity-normalized endpoint appearing in the common optimized tilt. -/
noncomputable def sourceCommonPairScaledEndpoint (t : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (sourceCommonPairIntensity t j / (2 / Real.pi)) * sourceCommonPairEndpoint t j

/-- The manuscript square-root normalization discharges the optimized exponent's matching identity. -/
theorem sourceCommonPairScaledEndpoint_match (t : ℝ) (j : ℕ)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) :
    sourceCommonPairIntensity t j * (sourceCommonPairEndpoint t j) ^ 2 =
      (2 / Real.pi) * (sourceCommonPairScaledEndpoint t j) ^ 2 := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hα := (sourceCommonPairIntensity_bounds t j hm).1
  unfold sourceCommonPairScaledEndpoint
  rw [mul_pow, Real.sq_sqrt (div_nonneg hα.le hg.le)]
  field_simp

theorem sourceCommonPairScaledEndpoint_pos (t : ℝ) (j : ℕ)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) (hq : 0 < sourceCommonPairEndpoint t j) :
    0 < sourceCommonPairScaledEndpoint t j := by
  unfold sourceCommonPairScaledEndpoint
  exact mul_pos (Real.sqrt_pos.mpr (div_pos (sourceCommonPairIntensity_bounds t j hm).1
    (by positivity))) hq

end SRWTightness
