import SRWTightness.DiskDiagonalLogBound
import SRWTightness.EquilibriumEnergySpacing

namespace SRWTightness

noncomputable def diskPointEnergyGapConstant : ℝ :=
  (2 * diskGreenEnergyConstant + 1 / 2) / (2 / Real.pi)

theorem diskPointEnergyGapConstant_pos : 0 < diskPointEnergyGapConstant := by
  unfold diskPointEnergyGapConstant
  have hB := diskGreenEnergyConstant_pos
  positivity

/-- The center-point time exceeds the innermost average time by log(a) with a uniform error. -/
theorem disk_point_energy_gap_log_bound (R a α : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R) :
    |pointEnergyTime (diskFinset R) 0 α (2 / Real.pi) -
      equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) - Real.log a| ≤
        diskPointEnergyGapConstant := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have ha0 : 0 < a := by linarith
  have hR0 : 0 < R := by linarith
  have hG := diskGreen_origin_log_bound R (by linarith)
  have hC := capacity_inverse_disk_log_bound R a ha hRa
  have he : diskGreen R 0 0 - 1 / capacity (diskFinset R) (diskFinset a) -
      (2 / Real.pi) * Real.log a =
      (diskGreen R 0 0 - (2 / Real.pi) * Real.log R) -
      (1 / capacity (diskFinset R) (diskFinset a) - (2 / Real.pi) * Real.log (R / a)) := by
    rw [Real.log_div hR0.ne' ha0.ne']
    ring
  have hh : |diskGreen R 0 0 - 1 / capacity (diskFinset R) (diskFinset a) -
      (2 / Real.pi) * Real.log a| ≤ 2 * diskGreenEnergyConstant := by
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have hs : |(diskGreen R 0 0 - 1 / capacity (diskFinset R) (diskFinset a) -
      (2 / Real.pi) * Real.log a) - 1 / 2| ≤ 2 * diskGreenEnergyConstant + 1 / 2 := by
    have hab := abs_sub (diskGreen R 0 0 - 1 / capacity (diskFinset R) (diskFinset a) -
      (2 / Real.pi) * Real.log a) (1 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hab
    linarith
  have hform : pointEnergyTime (diskFinset R) 0 α (2 / Real.pi) -
      equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) - Real.log a =
      ((diskGreen R 0 0 - 1 / capacity (diskFinset R) (diskFinset a) -
        (2 / Real.pi) * Real.log a) - 1 / 2) / (2 / Real.pi) := by
    unfold pointEnergyTime equilibriumEnergyTime diskGreen
    field_simp
    <;> ring
  rw [hform, abs_div, abs_of_pos hg]
  exact div_le_div_of_nonneg_right hs hg.le

theorem disk_point_energy_gap_ge_one (R a α : ℝ) (ha : 1 ≤ a) (hRa : 2 * a ≤ R)
    (hlog : 1 + diskPointEnergyGapConstant ≤ Real.log a) :
    1 ≤ pointEnergyTime (diskFinset R) 0 α (2 / Real.pi) -
      equilibriumEnergyTime (diskFinset R) (diskFinset a) α (2 / Real.pi) := by
  have hh := (abs_le.mp (disk_point_energy_gap_log_bound R a α ha hRa)).1
  linarith

end SRWTightness
