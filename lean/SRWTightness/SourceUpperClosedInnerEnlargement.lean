import SRWTightness.SourceUpperDiskEnlargement

open Filter MeasureTheory

namespace SRWTightness

/-- Literal closed half-radius event used in source (4.37). -/
def sourceUpperClosedInnerEvent (R s : ℝ) : Set Sample :=
  {ω | ∃ x : Site, Real.sqrt (normSq x) ≤ R / 2 ∧
    diskCenter R + s ≤ Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}

/-- The closed half-radius event embeds in the open half-radius event after doubling the killed disk. -/
theorem source_upper_closed_inner_enlargement (R s : ℝ) (hR : 1 < R) :
    sourceUpperClosedInnerEvent R s ≤ᵐ[pathLaw]
      {ω | ∃ x ∈ diskFinset ((2 * R) / 2),
        diskCenter (2 * R) + (s - sourceUpperDoublingShift) ≤
          Real.sqrt (localTime ω (exitSteps (2 * R) ω) x : ℝ)} := by
  filter_upwards [exitTime_ne_top_ae (by linarith : 0 ≤ R),
    exitTime_ne_top_ae (by linarith : 0 ≤ 2 * R)] with ω hi ho
  rintro ⟨x, hx, hh⟩
  have hxR : x ∈ diskFinset ((2 * R) / 2) := by
    apply (mem_diskFinset _ _).mpr
    rw [show (2 * R) / 2 = R by ring]
    have hnorm : Real.sqrt (normSq x) < R := by linarith
    exact (Real.sqrt_lt (normSq_nonneg x) (by linarith)).mp hnorm
  have htime := exitTime_mono_radius (by linarith : 0 ≤ R)
    (by linarith : R ≤ 2 * R) ω
  rw [← coe_exitSteps R ω hi, ← coe_exitSteps (2 * R) ω ho] at htime
  have hlocal := localTime_mono ω (WithTop.coe_le_coe.mp htime) x
  have hsqrt := Real.sqrt_le_sqrt (show (localTime ω (exitSteps R ω) x : ℝ) ≤
    localTime ω (exitSteps (2 * R) ω) x by exact_mod_cast hlocal)
  refine ⟨x, hxR, ?_⟩
  have hc := source_upper_doubling_center R hR
  linarith

/-- Actual probability comparison for the literal closed event. -/
theorem source_upper_closed_inner_probability (R s : ℝ) (hR : 1 < R) :
    pathLaw.real (sourceUpperClosedInnerEvent R s) ≤
      pathLaw.real {ω | ∃ x ∈ diskFinset ((2 * R) / 2),
        diskCenter (2 * R) + (s - sourceUpperDoublingShift) ≤
          Real.sqrt (localTime ω (exitSteps (2 * R) ω) x : ℝ)} := by
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (source_upper_closed_inner_enlargement R s hR))

end SRWTightness
