import SRWTightness.CommonSpatialCancellation

namespace SRWTightness

/-- The source dent absorbs the level count and t^26 prefactor with explicit polynomial decay. -/
theorem common_level_decay (t : ℝ) (ht : 1 ≤ t) :
    (t + 1) * t ^ 26 * Real.exp (-2000 * Real.log t) ≤ 2 / t ^ 1973 := by
  have ht0 : 0 < t := by linarith
  have he : Real.exp (-2000 * Real.log t) = (t ^ 2000)⁻¹ := by
    rw [show -2000 * Real.log t = -(2000 * Real.log t) by ring, Real.exp_neg,
      show (2000 : ℝ) = (2000 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log ht0]
  calc
    _ ≤ (2 * t) * t ^ 26 * Real.exp (-2000 * Real.log t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
        (Real.exp_nonneg _)
    _ = 2 / t ^ 1973 := by
      rw [he]
      field_simp
      <;> ring

end SRWTightness
