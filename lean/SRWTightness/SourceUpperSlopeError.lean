import SRWTightness.SourceUpperMarkParameters

namespace SRWTightness

/-- Uniform height bounds in the source range 0<=s<=log(t). -/
theorem source_upper_height_bounds (t s : ℝ) (ht : 0 < t)
    (hs : 0 ≤ s) (hslog : s ≤ Real.log t) :
    t ≤ sourceUpperHeight t s ∧
      sourceUpperHeight t s ≤ 2 * t + Real.sqrt Real.pi * Real.log t := by
  have hl : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht).trans (by linarith)
  have hp : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log t := hs.trans hslog
  unfold sourceUpperHeight
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hslog hp]

/-- Total-depth drift controls the slope uniformly over the manuscript height range. -/
theorem source_upper_slope_error (t s B : ℝ) (ht : 0 < t)
    (hs : 0 ≤ s) (hslog : s ≤ Real.log t)
    (hT : t / 2 ≤ sourceUpperTotalDepth t)
    (hB : |sourceUpperTotalDepth t - t| ≤ B) :
    |sourceUpperSlope t s - 2| ≤
      2 * ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / t := by
  have hT0 : 0 < sourceUpperTotalDepth t := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hlog : 0 ≤ Real.log t := hs.trans hslog
  have hp : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hb := abs_le.mp hB
  have hprod := mul_le_mul_of_nonneg_left hslog hp
  have hn : |sourceUpperHeight t s - 2 * sourceUpperTotalDepth t| ≤
      (1 + Real.sqrt Real.pi) * Real.log t + 2 * B := by
    unfold sourceUpperHeight
    apply abs_le.mpr
    constructor <;> nlinarith
  have he : sourceUpperSlope t s - 2 =
      (sourceUpperHeight t s - 2 * sourceUpperTotalDepth t) / sourceUpperTotalDepth t := by
    unfold sourceUpperSlope
    field_simp
  rw [he, abs_div, abs_of_pos hT0]
  calc
    _ ≤ ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / sourceUpperTotalDepth t :=
      div_le_div_of_nonneg_right hn hT0.le
    _ ≤ ((1 + Real.sqrt Real.pi) * Real.log t + 2 * B) / (t / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hT
    _ = _ := by ring

end SRWTightness
