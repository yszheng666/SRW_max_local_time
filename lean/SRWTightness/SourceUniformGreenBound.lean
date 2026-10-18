import SRWTightness.SourceLowerTime
import SRWTightness.DiskCapacityLogBound
import SRWTightness.DiskDiagonalLogBound

namespace SRWTightness

/-- A diagonal Green bound uniform over every point of a translated disk. -/
theorem translated_disk_diagonal_upper (b : Site) (R : ℝ) (hR : 1 ≤ R) (z : Site)
    (hz : z ∈ translateFinset b (diskFinset R)) :
    killedGreen (translateFinset b (diskFinset R)) z z ≤
      (2 / Real.pi) * Real.log R + (diskGreenEnergyConstant + (2 / Real.pi) * Real.log 2) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  rw [killedGreen_translate]
  exact diskGreen_diagonal_upper R hR x (by simpa only [mem_diskFinset] using hx)

noncomputable def sourceUniformGreenScale (m : ℝ) : ℝ :=
  (2 / Real.pi) * sourceLowerTime m +
    (diskGreenEnergyConstant + (2 / Real.pi) * (sourceLowerTimeError + Real.log 4 + Real.log 2))

/-- The source disk has a uniform O(d) diagonal bound, with an explicit positive scale. -/
theorem source_uniform_green_bound (b : Site) (m H : ℝ) (hm : 2 ≤ m) (hH : 0 ≤ H)
    (hHm : 5 * H ≤ m) :
    1 ≤ sourceUniformGreenScale m ∧
    ∀ z ∈ translateFinset b (diskFinset (Real.exp 1 * m + H)),
      killedGreen (translateFinset b (diskFinset (Real.exp 1 * m + H))) z z ≤
        sourceUniformGreenScale m := by
  have hm0 : 0 < m := by linarith
  have hR : 1 ≤ Real.exp 1 * m + H := by nlinarith [Real.exp_one_gt_two]
  have hR4 : Real.exp 1 * m + H ≤ 4 * m := by nlinarith [Real.exp_one_lt_three]
  have hl := Real.log_le_log (by linarith : 0 < Real.exp 1 * m + H) hR4
  rw [Real.log_mul (by norm_num) hm0.ne'] at hl
  have hd := (abs_le.mp (sourceLowerTime_log_bound m hm)).1
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hu (z : Site) (hz : z ∈ translateFinset b (diskFinset (Real.exp 1 * m + H))) :
      killedGreen (translateFinset b (diskFinset (Real.exp 1 * m + H))) z z ≤
        sourceUniformGreenScale m := by
    have hh := translated_disk_diagonal_upper b _ hR z hz
    have hlog := mul_le_mul_of_nonneg_left hl hg.le
    have htime := mul_le_mul_of_nonneg_left (show Real.log m ≤ sourceLowerTime m + sourceLowerTimeError by linarith) hg.le
    unfold sourceUniformGreenScale
    linarith
  have hz : b ∈ translateFinset b (diskFinset (Real.exp 1 * m + H)) := by
    have hh := (mem_translateFinset_add b (diskFinset (Real.exp 1 * m + H)) 0).mpr
      (zero_mem_diskFinset _ (by linarith))
    simpa only [add_zero] using hh
  exact ⟨(killedGreen_diag_ge_one _ b hz).trans (hu b hz), hu⟩

end SRWTightness
