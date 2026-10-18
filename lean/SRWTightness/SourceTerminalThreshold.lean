import SRWTightness.RoundedTerminalThreshold
import SRWTightness.SourceReferenceIntensityLimit
import SRWTightness.SourceTiltIntensityBound
import SRWTightness.Targets

namespace SRWTightness

noncomputable def sourceTerminalHeight (t : ℝ) : ℝ := 2 * t - Real.log t

noncomputable def sourceTerminalVisitCutoff (t : ℝ) : ℕ :=
  Nat.ceil (sourceTerminalHeight t ^ 2 / Real.pi)

noncomputable def sourceTerminalThreshold (t u : ℝ) : ℝ :=
  terminalOccupationThreshold (sourceTerminalVisitCutoff t)
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) u

/-- The actual source count cutoff is the natural ceiling of the squared disk centering. -/
theorem sourceTerminalVisitCutoff_at_radius (R : ℝ) :
    sourceTerminalVisitCutoff (Real.log R) = Nat.ceil (diskCenter R ^ 2) := by
  have he : diskCenter R = sourceTerminalHeight (Real.log R) / Real.sqrt Real.pi := by
    unfold diskCenter sourceTerminalHeight
    ring
  rw [he, div_pow, Real.sq_sqrt Real.pi_pos.le]
  rfl

theorem sourceTerminalVisitCutoff_green_form (t : ℝ) :
    sourceTerminalVisitCutoff t = Nat.ceil ((2 / Real.pi) * sourceTerminalHeight t ^ 2 / 2) := by
  unfold sourceTerminalVisitCutoff
  congr 1
  ring

/-- The threshold agrees with the normalized integer visit window whenever u squared over two is k. -/
theorem sourceTerminalThreshold_visit_formula (t u : ℝ) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    sourceTerminalThreshold t u =
      ((sourceTerminalVisitCutoff t : ℝ) - sourceReferenceIntensity (sourceLowerRadius t) 14 * k) /
        (u * Real.sqrt (sourceReferenceIntensity (sourceLowerRadius t) 14 * (2 / Real.pi))) := by
  simp only [sourceTerminalThreshold, terminalOccupationThreshold, hk]

/-- Explicit rounding and intensity error for the exact source threshold. -/
theorem sourceTerminalThreshold_ideal_error (t u : ℝ)
    (ht : sourceScaleThreshold 4 ≤ t) (hu : 0 < u) :
    |sourceTerminalThreshold t u - (sourceTerminalHeight t ^ 2 - u ^ 2) / (2 * u)| ≤
      1 / (u * (2 / Real.pi)) +
        28 * (sourceTerminalHeight t ^ 2 + u ^ 2) / (u * sourceLowerRadius t) := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  have hα := sourceReferenceIntensity_ge_greenConstant (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)
  have haerr := (le_abs_self _).trans (sourceReferenceIntensity_profile_error t ht)
  have he := terminalThreshold_rounded_error
    (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) u
    (sourceTerminalHeight t) hg hα hu
  rw [sourceTerminalThreshold, sourceTerminalVisitCutoff_green_form]
  refine he.trans ?_
  refine add_le_add (le_refl _) ?_
  calc
    _ ≤ ((56 * (2 / Real.pi)) / sourceLowerRadius t) *
        (sourceTerminalHeight t ^ 2 + u ^ 2) / (2 * u * (2 / Real.pi)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right haerr
        (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by positivity)
    _ = _ := by field_simp; ring

end SRWTightness
