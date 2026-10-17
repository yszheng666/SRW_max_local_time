import SRWTightness.SourceUpperInnerReduction

open Filter MeasureTheory

namespace SRWTightness

/-- Integer local-time cutoffs agree with square-root thresholds at nonnegative heights. -/
theorem source_upper_ceil_sq_iff_sqrt (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    Nat.ceil (a ^ 2) ≤ n ↔ a ≤ Real.sqrt (n : ℝ) := by
  rw [Nat.ceil_le, Real.le_sqrt ha (by positivity)]

/-- The source centered height is eventually nonnegative at every nonnegative excess. -/
theorem source_upper_center_nonneg (R s : ℝ) (ht : 2 ≤ Real.log R) (hs : 0 ≤ s) :
    0 ≤ diskCenter R + s := by
  rw [sourceUpperHeight_at_radius]
  apply div_nonneg _ (Real.sqrt_nonneg _)
  unfold sourceUpperHeight
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log R)
  have hmul : 0 ≤ Real.sqrt Real.pi * s := mul_nonneg (Real.sqrt_nonneg _) hs
  linarith

/-- The inner event matches the square-root local-time event on the open half-radius disk. -/
theorem source_upper_inner_event_at_radius (R s : ℝ) (hR : 0 < R)
    (ht : 2 ≤ Real.log R) (hs : 0 ≤ s) :
    sourceUpperInnerHighEvent (Real.log R) s =
      {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + s ≤
        Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)} := by
  ext ω
  simp only [sourceUpperInnerHighEvent, Set.mem_setOf_eq,
    sourceUpperVisitCutoff_at_radius, Real.exp_log hR, domainLocalTime_disk,
    source_upper_ceil_sq_iff_sqrt _ (source_upper_center_nonneg R s ht hs)]

end SRWTightness
