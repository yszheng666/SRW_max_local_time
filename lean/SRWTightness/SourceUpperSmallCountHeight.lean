import SRWTightness.SourceUpperMarkParameters

namespace SRWTightness

/-- Rounding the occupation cutoff upwards preserves the normalized height. -/
theorem rounded_gaussian_threshold_lower (g y : ℝ) (hg : 0 < g) :
    y ≤ Real.sqrt (2 * (Nat.ceil (g * y ^ 2 / 2) : ℝ) / g) := by
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hg).mpr
  have hc := Nat.le_ceil (g * y ^ 2 / 2)
  nlinarith

/-- Below the coarse count t-1, the actual positive Gaussian threshold stays linear in t. -/
theorem source_upper_small_count_height (t s u : ℝ) (ht : 0 < t) (hs : 0 ≤ s)
    (hlog : Real.log t ≤ t / 10) (hu0 : 0 ≤ u) (hu : u ≤ t - 1)
    (hsize : 5 * sourceUpperBuffer t ≤ sourceUpperRadius t) :
    t / 10 ≤ Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ) / (2 / Real.pi)) -
      Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) * u := by
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer upperTerminalFineRadius
    positivity
  have he := source_reference_sqrt_error
    (sourceUpperRadius t) (sourceUpperBuffer t) hm hH hsize
  have hratio : 4 * sourceUpperBuffer t / sourceUpperRadius t ≤ 4 / 5 := by
    apply (div_le_iff₀ hm).mpr
    linarith
  have hb : Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) ≤ 9 / 5 := by
    change |Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) - 1| ≤ _ at he
    have := (abs_le.mp he).2
    linarith
  have hprod := mul_le_mul_of_nonneg_right hb hu0
  have hround := rounded_gaussian_threshold_lower (2 / Real.pi)
    (sourceUpperHeight t s) (by positivity)
  rw [← sourceUpperVisitCutoff_green_form] at hround
  have hheight : 19 * t / 10 ≤ sourceUpperHeight t s := by
    unfold sourceUpperHeight
    have := mul_nonneg (Real.sqrt_nonneg Real.pi) hs
    linarith
  linarith

end SRWTightness
