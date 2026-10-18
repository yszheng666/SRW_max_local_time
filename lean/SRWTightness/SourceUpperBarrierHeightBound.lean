import SRWTightness.SourceUpperSlopeError
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SRWTightness

/-- The source terminal barrier confines its square-root count to a fixed linear range. -/
theorem source_upper_barrier_height_bound (t s u : ℝ) (ht : 1 ≤ t)
    (hs : 0 ≤ s) (hslog : s ≤ Real.log t) (hu : 0 ≤ u)
    (hT : 0 < sourceUpperTotalDepth t)
    (hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hdt : upperTerminalDepth (sourceUpperLogRadius t) ≤ t)
    (hbar : u ≤ sourceUpperTarget t s + (4 + s) +
      upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) :
    |u| ≤ (8 + Real.sqrt Real.pi) * t := by
  have ht0 : 0 < t := by linarith
  have hy := source_upper_height_bounds t s ht0 hs hslog
  have hθ : 0 ≤ sourceUpperSlope t s := div_nonneg (by linarith [hy.1]) hT.le
  have hmul : sourceUpperSlope t s * sourceUpperTotalDepth t = sourceUpperHeight t s :=
    div_mul_cancel₀ _ hT.ne'
  have hx : sourceUpperTarget t s ≤ sourceUpperHeight t s := by
    unfold sourceUpperTarget
    unfold sourceUpperTotalDepth at hmul
    nlinarith [mul_nonneg hθ (show 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) by linarith)]
  have hroot : upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) ≤
      upperTerminalDepth (sourceUpperLogRadius t) :=
    Real.rpow_le_self_of_one_le hd (by norm_num)
  have hlog : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hp := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg Real.pi)
  rw [abs_of_nonneg hu]
  nlinarith [hy.2]

end SRWTightness
