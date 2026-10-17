import SRWTightness.SourceUpperRoundedThreshold
import SRWTightness.SourceUpperVisitThreshold
import SRWTightness.SourceUpperTerminalScaleConditions
import SRWTightness.SourceRootDepth

namespace SRWTightness

noncomputable def sourceUpperRadius (t : ℝ) : ℝ := Real.exp (sourceUpperLogRadius t)

noncomputable def sourceUpperBuffer (t : ℝ) : ℝ :=
  4 * upperTerminalFineRadius (sourceUpperLogRadius t) + 10

noncomputable def sourceUpperIntensity (t : ℝ) : ℝ :=
  sourceReferenceIntensity (sourceUpperRadius t) (sourceUpperBuffer t)

/-- The natural coarse depth is used in the large-radius regime where ell is positive. -/
noncomputable def sourceUpperCoarseDepth (t : ℝ) : ℕ :=
  sourceRootDepth (Real.exp t) (sourceUpperRadius t) - 1

noncomputable def sourceUpperTotalDepth (t : ℝ) : ℝ :=
  (sourceUpperCoarseDepth t : ℝ) + upperTerminalDepth (sourceUpperLogRadius t)

noncomputable def sourceUpperSlope (t s : ℝ) : ℝ :=
  sourceUpperHeight t s / sourceUpperTotalDepth t

noncomputable def sourceUpperTarget (t s : ℝ) : ℝ :=
  sourceUpperSlope t s * (sourceUpperCoarseDepth t : ℝ)

/-- Apply the threshold expansion to the actual upper-tail parameters and integer cutoff. -/
theorem source_upper_actual_threshold_error (t s u : ℝ)
    (hsize : 5 * sourceUpperBuffer t ≤ sourceUpperRadius t)
    (hy : 0 < sourceUpperHeight t s) (hT : sourceUpperTotalDepth t ≠ 0)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    ∃ ε : ℝ,
      Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ) / (2 / Real.pi)) -
        Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) * u =
        2 * upperTerminalDepth (sourceUpperLogRadius t) + (sourceUpperTarget t s - u) + ε ∧
      |ε| ≤ 2 / ((2 / Real.pi) * sourceUpperHeight t s) +
        |sourceUpperSlope t s - 2| * upperTerminalDepth (sourceUpperLogRadius t) +
        (4 * sourceUpperBuffer t / sourceUpperRadius t) * |u| := by
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer upperTerminalFineRadius
    positivity
  have hid : sourceUpperHeight t s = sourceUpperSlope t s *
      ((sourceUpperCoarseDepth t : ℝ) + upperTerminalDepth (sourceUpperLogRadius t)) := by
    change sourceUpperHeight t s =
      (sourceUpperHeight t s / sourceUpperTotalDepth t) * sourceUpperTotalDepth t
    rw [div_mul_cancel₀ _ hT]
  have he := source_upper_rounded_threshold_error
    (sourceUpperRadius t) (sourceUpperBuffer t) u (sourceUpperHeight t s)
    (sourceUpperSlope t s) (sourceUpperCoarseDepth t : ℝ)
    (upperTerminalDepth (sourceUpperLogRadius t)) (sourceUpperTarget t s)
    (sourceUpperTarget t s - u) |u| |sourceUpperSlope t s - 2|
    (Real.exp_pos _) hH hsize hy hd le_rfl le_rfl hid rfl rfl
  simpa only [sourceUpperVisitCutoff_green_form, sourceUpperIntensity] using he

end SRWTightness
