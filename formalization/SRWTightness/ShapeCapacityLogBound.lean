import SRWTightness.DiskCapacityLogBound
import SRWTightness.CapacityMonotone

namespace SRWTightness

/-- A uniform energy estimate for every finite shape between two comparable disks. -/
theorem capacity_inverse_shape_log_bound (R a : ℝ) (ha : 2 ≤ a) (hRa : 4 * a ≤ R)
    (K : Finset Site) (hinner : diskFinset (a / 2) ⊆ K) (houter : K ⊆ diskFinset (2 * a)) :
    |1 / capacity (diskFinset R) K - (2 / Real.pi) * Real.log (R / a)| ≤
      diskGreenEnergyConstant + (2 / Real.pi) * Real.log 2 := by
  have ha0 : 0 < a := by linarith
  have hR0 : 0 < R := by linarith
  have hOD : diskFinset (2 * a) ⊆ diskFinset R := diskFinset_mono _ _ (by positivity) (by linarith)
  have hKD := houter.trans hOD
  have hneI : (diskFinset (a / 2)).Nonempty := ⟨0, zero_mem_diskFinset _ (by positivity)⟩
  have hneK : K.Nonempty := hneI.mono hinner
  have hl := capacity_inverse_mono_set (diskFinset R) K (diskFinset (2 * a)) houter hOD hneK
  have hu := capacity_inverse_mono_set (diskFinset R) (diskFinset (a / 2)) K hinner hKD hneI
  have hbO := abs_le.mp (capacity_inverse_disk_log_bound R (2 * a) (by linarith) (by linarith))
  have hbI := abs_le.mp (capacity_inverse_disk_log_bound R (a / 2) (by linarith) (by linarith))
  have hlogO : Real.log (R / (2 * a)) = Real.log (R / a) - Real.log 2 := by
    rw [Real.log_div hR0.ne' (mul_ne_zero (by norm_num) ha0.ne'),
      Real.log_mul (by norm_num) ha0.ne', Real.log_div hR0.ne' ha0.ne']
    ring
  have hlogI : Real.log (R / (a / 2)) = Real.log (R / a) + Real.log 2 := by
    rw [Real.log_div hR0.ne' (div_ne_zero ha0.ne' (by norm_num)),
      Real.log_div ha0.ne' (by norm_num), Real.log_div hR0.ne' ha0.ne']
    ring
  rw [hlogO] at hbO
  rw [hlogI] at hbI
  exact abs_le.mpr ⟨by nlinarith [hbO.1], by nlinarith [hbI.2]⟩

end SRWTightness
