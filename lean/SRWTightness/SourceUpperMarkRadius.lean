import SRWTightness.SourceUpperThresholdConditions

open Filter
namespace SRWTightness

/-- The padded killing radius of the source reference marks, distinct from the depth disk. -/
noncomputable def sourceUpperMarkRadius (t : ℝ) : ℝ :=
  Real.exp 1 * sourceUpperRadius t + sourceUpperBuffer t

/-- The actual padded disk is a bounded enlargement of the disk defining reference depth. -/
theorem source_upper_mark_radius_bounds (t : ℝ)
    (hsize : 5 * sourceUpperBuffer t ≤ sourceUpperRadius t) :
    2 ≤ upperTerminalRadius (sourceUpperLogRadius t) ∧
      upperTerminalRadius (sourceUpperLogRadius t) ≤ sourceUpperMarkRadius t ∧
      sourceUpperMarkRadius t ≤ 16 * upperTerminalRadius (sourceUpperLogRadius t) := by
  have hH : 10 ≤ sourceUpperBuffer t := by
    have hr : 0 ≤ upperTerminalFineRadius (sourceUpperLogRadius t) :=
      Nat.cast_nonneg _
    unfold sourceUpperBuffer
    linarith
  have hm : 0 ≤ sourceUpperRadius t := (Real.exp_pos _).le
  have he : upperTerminalRadius (sourceUpperLogRadius t) =
      Real.exp 1 * sourceUpperRadius t - 1 := by
    unfold upperTerminalRadius sourceUpperRadius
    rw [Real.exp_add]
    ring
  have hexp := mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le hm
  rw [he]
  unfold sourceUpperMarkRadius
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The padded radius has the same reference depth up to a fixed logarithmic error. -/
theorem source_upper_mark_radius_depth_error (t : ℝ)
    (hsize : 5 * sourceUpperBuffer t ≤ sourceUpperRadius t) :
    |upperTerminalDepth (sourceUpperLogRadius t) - Real.log (sourceUpperMarkRadius t)| ≤
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 16 := by
  obtain ⟨hR, hlo, hhi⟩ := source_upper_mark_radius_bounds t hsize
  have hd := disk_normalized_reference_log_bound
    (upperTerminalRadius (sourceUpperLogRadius t)) hR
  exact terminal_outer_log_error _ _ _ _ (by linarith) hlo hhi hd

end SRWTightness
