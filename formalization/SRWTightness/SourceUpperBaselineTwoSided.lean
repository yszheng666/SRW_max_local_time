import SRWTightness.SourceUpperBaselineLower
import SRWTightness.SourceUpperCoarseLinearDepth
import SRWTightness.SourceUpperDepthInternal

open Filter
open scoped Topology
namespace SRWTightness

/-- The exact baseline error has a uniform two-sided bound, including its positive square. -/
theorem source_upper_baseline_two_sided (t s B : ℝ) (ht : 1 ≤ t) (hB0 : 0 ≤ B)
    (hBt : B ≤ t) (hs : 0 ≤ s) (hslog : s ≤ Real.log t)
    (hT : t / 2 ≤ sourceUpperTotalDepth t) (hB : |sourceUpperTotalDepth t - t| ≤ B)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hN : (sourceUpperCoarseDepth t : ℝ) ≠ 0) :
    let Z := (1 + Real.sqrt Real.pi) * Real.log t + 2 * B
    let H := 6 + Real.sqrt Real.pi
    |sourceUpperTarget t s ^ 2 / (2 * sourceUpperCoarseDepth t) -
      (2 * t - 2 * upperTerminalDepth (sourceUpperLogRadius t) - 2 * Real.log t +
        2 * Real.sqrt Real.pi * s - 2 * (sourceUpperTotalDepth t - t))| ≤
      Z ^ 2 / t + 2 * H * upperTerminalDepth (sourceUpperLogRadius t) * Z / t := by
  dsimp only
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
  have hz : |z| ≤ Z := by
    apply abs_le.mpr
    dsimp [z, Z, T, sourceUpperHeight]
    have hm := mul_le_mul_of_nonneg_left hslog (Real.sqrt_nonneg Real.pi)
    have hm0 := mul_nonneg (Real.sqrt_nonneg Real.pi) hs
    constructor <;> nlinarith
  have hy := source_upper_height_bounds t s ht0 hs hslog
  have hy0 : 0 ≤ sourceUpperHeight t s + 2 * T := by dsimp [T]; linarith [hy.1]
  have hyH : sourceUpperHeight t s + 2 * T ≤ H * t := by
    have hl : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
    have hm := mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg Real.pi)
    dsimp [T, H]
    nlinarith [hy.2]
  have hnum : d * |z| * (sourceUpperHeight t s + 2 * T) ≤ d * Z * (H * t) := by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hd) hy0).trans
    exact mul_le_mul_of_nonneg_left hyH (mul_nonneg hd hZ)
  have hden : t ^ 2 / 2 ≤ 2 * T ^ 2 := by dsimp [T]; nlinarith
  have hfrac : |d * z * (sourceUpperHeight t s + 2 * T) / (2 * T ^ 2)| ≤
      2 * H * d * Z / t := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hd, abs_of_nonneg hy0,
      abs_of_pos (by dsimp [T]; positivity : 0 < 2 * T ^ 2)]
    calc
      _ ≤ (d * Z * (H * t)) / (2 * T ^ 2) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (d * Z * (H * t)) / (t ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by field_simp
  have hsq : z ^ 2 ≤ Z ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg z) hz
    nlinarith [sq_abs z]
  have hfirst : |z ^ 2 / (2 * T)| ≤ Z ^ 2 / t := by
    rw [abs_of_nonneg (by dsimp [T]; positivity : 0 ≤ z ^ 2 / (2 * T))]
    exact (div_le_div_of_nonneg_right hsq (by positivity)).trans
      (div_le_div_of_nonneg_left (sq_nonneg Z) ht0 (by dsimp [T]; linarith))
  have he := source_upper_baseline_quadratic t s hT0.ne' hN
  dsimp only at he
  rw [he]
  have herr := (abs_sub (z ^ 2 / (2 * T))
    (d * z * (sourceUpperHeight t s + 2 * T) / (2 * T ^ 2))).trans
      (add_le_add hfirst hfrac)
  simpa only [z, T, d, Z, H, add_sub_cancel_left] using herr

end SRWTightness
