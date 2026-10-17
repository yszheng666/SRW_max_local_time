import SRWTightness.SourceUpperBaselineQuadratic
import SRWTightness.SourceUpperSlopeError

namespace SRWTightness

/-- An explicit one-sided baseline error sufficient for the source upper exponential bound. -/
theorem source_upper_baseline_lower (t s B : ℝ) (ht : 1 ≤ t) (hB0 : 0 ≤ B) (hBt : B ≤ t)
    (hs : 0 ≤ s) (hslog : s ≤ Real.log t)
    (hT : t / 2 ≤ sourceUpperTotalDepth t) (hB : |sourceUpperTotalDepth t - t| ≤ B)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hN : (sourceUpperCoarseDepth t : ℝ) ≠ 0) :
    2 * t - 2 * upperTerminalDepth (sourceUpperLogRadius t) - 2 * Real.log t +
      2 * Real.sqrt Real.pi * s - 2 * B -
      2 * (6 + Real.sqrt Real.pi) * upperTerminalDepth (sourceUpperLogRadius t) *
        ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / t ≤
      sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) := by
  have ht0 : 0 < t := by linarith
  have hT0 : 0 < sourceUpperTotalDepth t := by linarith
  let T := sourceUpperTotalDepth t
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let z := sourceUpperHeight t s - 2 * T
  let Z := (1 + Real.sqrt Real.pi) * Real.log t + 2 * B
  let H := 6 + Real.sqrt Real.pi
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hb := abs_le.mp hB
  have hz : z ≤ Z := by
    dsimp [z, Z, T, sourceUpperHeight]
    have hm := mul_le_mul_of_nonneg_left hslog (Real.sqrt_nonneg Real.pi)
    nlinarith
  have hy := source_upper_height_bounds t s ht0 hs hslog
  have hy0 : 0 ≤ sourceUpperHeight t s + 2 * T := by dsimp [T]; linarith [hy.1]
  have hyH : sourceUpperHeight t s + 2 * T ≤ H * t := by
    have hl : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
    have hm := mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg Real.pi)
    dsimp [T, H]
    nlinarith [hy.2]
  have hnum : d * z * (sourceUpperHeight t s + 2 * T) ≤ d * Z * (H * t) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hd) hy0).trans
    exact mul_le_mul_of_nonneg_left hyH (mul_nonneg hd hZ)
  have hden : t ^ 2 / 2 ≤ 2 * T ^ 2 := by dsimp [T]; nlinarith
  have hfrac : d * z * (sourceUpperHeight t s + 2 * T) / (2 * T ^ 2) ≤
      2 * H * d * Z / t := by
    calc
      _ ≤ (d * Z * (H * t)) / (2 * T ^ 2) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (d * Z * (H * t)) / (t ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp <;> ring
  have hpos : 0 ≤ z ^ 2 / (2 * T) := by dsimp [T]; positivity
  have he := source_upper_baseline_quadratic t s hT0.ne' hN
  dsimp only at he
  dsimp [T, d, z, H, Z] at hfrac hpos
  rw [he]
  linarith

end SRWTightness
