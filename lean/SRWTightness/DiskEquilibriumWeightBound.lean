import SRWTightness.DiskEquilibriumMeasureBound
import SRWTightness.DiskCapacityLogBound

namespace SRWTightness

noncomputable def diskEquilibriumWeightConstant : ℝ :=
  (16 / 3) * diskGreenEnergyConstant *
    (1 + diskGreenEnergyConstant / ((2 / Real.pi) * Real.log 2))

theorem diskEquilibriumWeightConstant_pos : 0 < diskEquilibriumWeightConstant := by
  unfold diskEquilibriumWeightConstant
  have hB := diskGreenEnergyConstant_pos
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- A uniform inverse-radius bound for actual normalized equilibrium weights. -/
theorem equilibriumWeight_disk_radius_upper (a R : ℝ) (ha : 4 ≤ a)
    (hRa : 2 * a ≤ R) (x : Site) :
    equilibriumWeight (diskFinset R) (diskFinset a) x ≤ diskEquilibriumWeightConstant / a := by
  have ha0 : 0 < a := by linarith
  let L := (2 / Real.pi) * Real.log (R / a)
  let L0 := (2 / Real.pi) * Real.log 2
  let B := diskGreenEnergyConstant
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hL0 : 0 < L0 := mul_pos hg (Real.log_pos (by norm_num))
  have hLL : L0 ≤ L := by
    apply mul_le_mul_of_nonneg_left _ hg.le
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ ha0).mpr hRa
  have hL : 0 < L := hL0.trans_le hLL
  have hB : 0 < B := diskGreenEnergyConstant_pos
  have hKD := diskFinset_mono a R ha0.le (by linarith)
  have hne : (diskFinset a).Nonempty := ⟨0, zero_mem_diskFinset a ha0⟩
  have hc := capacity_pos _ _ hKD hne
  have hcap := (abs_le.mp (capacity_inverse_disk_log_bound R a (by linarith) hRa)).2
  have hcapUpper : 1 / capacity (diskFinset R) (diskFinset a) ≤ L + B := by
    dsimp [L, B]
    linarith
  have he := equilibriumMeasure_disk_boundary_upper a R ha hRa x
  have hh : equilibriumWeight (diskFinset R) (diskFinset a) x ≤
      (B / L * (16 / (3 * a))) * (L + B) := by
    unfold equilibriumWeight
    rw [div_eq_mul_one_div]
    exact mul_le_mul he hcapUpper (by positivity)
      (mul_nonneg (div_nonneg hB.le hL.le) (by positivity))
  have hratio : B / L ≤ B / L0 := div_le_div_of_nonneg_left hB.le hL0 hLL
  have hr : (B / L * (16 / (3 * a))) * (L + B) =
      ((16 / 3) * B / a) * (1 + B / L) := by
    field_simp
    <;> ring
  rw [hr] at hh
  calc
    _ ≤ ((16 / 3) * B / a) * (1 + B / L) := hh
    _ ≤ ((16 / 3) * B / a) * (1 + B / L0) :=
      mul_le_mul_of_nonneg_left (add_le_add_right hratio 1) (by positivity)
    _ = diskEquilibriumWeightConstant / a := by
      unfold diskEquilibriumWeightConstant
      dsimp [B, L0]
      ring

end SRWTightness
