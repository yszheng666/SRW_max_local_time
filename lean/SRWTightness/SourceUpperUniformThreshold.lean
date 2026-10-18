import SRWTightness.SourceUpperSlopeError

namespace SRWTightness

/-- Explicit source-order error, uniformly in the prescribed s range and |u|<=U*t. -/
theorem source_upper_uniform_threshold_error (t s u B U : ℝ)
    (ht : 0 < t) (hlog : 1 ≤ Real.log t) (hs : 0 ≤ s) (hslog : s ≤ Real.log t)
    (hsize : 5 * sourceUpperBuffer t ≤ sourceUpperRadius t)
    (hT : t / 2 ≤ sourceUpperTotalDepth t)
    (hB : |sourceUpperTotalDepth t - t| ≤ B) (hU : 0 ≤ U) (hu : |u| ≤ U * t)
    (hr : 1 ≤ upperTerminalFineRadius (sourceUpperLogRadius t))
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    ∃ ε : ℝ,
      Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ) / (2 / Real.pi)) -
        Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) * u =
        2 * upperTerminalDepth (sourceUpperLogRadius t) + (sourceUpperTarget t s - u) + ε ∧
      |ε| ≤ (2 / (2 / Real.pi)) / t +
        (2 * (1 + Real.sqrt Real.pi + 2 * B)) *
          (upperTerminalDepth (sourceUpperLogRadius t) * Real.log t / t) +
        (56 * U) * (t * upperTerminalFineRadius (sourceUpperLogRadius t) /
          sourceUpperRadius t) := by
  have hheight := (source_upper_height_bounds t s ht hs hslog).1
  have hy : 0 < sourceUpperHeight t s := ht.trans_le hheight
  have hT0 : 0 < sourceUpperTotalDepth t := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hm : 0 < sourceUpperRadius t := Real.exp_pos _
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  obtain ⟨ε, heq, he⟩ := source_upper_actual_threshold_error t s u hsize hy hT0.ne' hd
  refine ⟨ε, heq, he.trans ?_⟩
  have hround : 2 / ((2 / Real.pi) * sourceUpperHeight t s) ≤
      (2 / (2 / Real.pi)) / t := by
    calc
      _ ≤ 2 / ((2 / Real.pi) * t) := div_le_div_of_nonneg_left (by norm_num)
        (mul_pos hg ht) (mul_le_mul_of_nonneg_left hheight hg.le)
      _ = _ := by ring
  have hslope : |sourceUpperSlope t s - 2| ≤
      (2 * (1 + Real.sqrt Real.pi + 2 * B)) * Real.log t / t := by
    refine (source_upper_slope_error t s B ht hs hslog hT hB).trans ?_
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith [mul_le_mul_of_nonneg_left hlog hB0]
  have hbuffer : sourceUpperBuffer t ≤
      14 * upperTerminalFineRadius (sourceUpperLogRadius t) := by
    unfold sourceUpperBuffer
    linarith
  have hcoeff : 4 * sourceUpperBuffer t / sourceUpperRadius t ≤
      56 * upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  have hmark := mul_le_mul hcoeff hu (abs_nonneg u) (by positivity :
    0 ≤ 56 * upperTerminalFineRadius (sourceUpperLogRadius t) / sourceUpperRadius t)
  have hsum := add_le_add
    (add_le_add hround (mul_le_mul_of_nonneg_right hslope hd)) hmark
  convert hsum using 1 <;> ring

end SRWTightness
