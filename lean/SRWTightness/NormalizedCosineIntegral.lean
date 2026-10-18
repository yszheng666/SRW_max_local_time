import SRWTightness.PoissonCosineIntegral

namespace SRWTightness

/-- The cosine resolvent integral, parameterized by the positive complementary sine. -/
theorem normalized_cosine_integral (a s : ℝ) (hs : 0 < s) (hc : a ^ 2 + s ^ 2 = 1) :
    (∫ t in 0..2 * Real.pi, 1 / (1 - a * Real.cos t)) = 2 * Real.pi / s := by
  have ha : |a| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg a, sq_pos_of_pos hs]
  have hsp : 0 < 1 + s := by linarith
  have hsn : 1 + s ≠ 0 := ne_of_gt hsp
  let r := a / (1 + s)
  have hr : |r| < 1 := by
    dsimp [r]
    rw [abs_div, abs_of_pos hsp]
    exact (div_lt_one hsp).mpr (by linarith)
  have hn : 1 - r ^ 2 = 2 * s / (1 + s) := by
    dsimp [r]
    field_simp [hsn]
    nlinarith
  have hd (t : ℝ) : 1 + r ^ 2 - 2 * r * Real.cos t =
      2 / (1 + s) * (1 - a * Real.cos t) := by
    dsimp [r]
    field_simp [hsn]
    nlinarith
  have hpoint (t : ℝ) : (1 - r ^ 2) / (1 + r ^ 2 - 2 * r * Real.cos t) =
      s * (1 / (1 - a * Real.cos t)) := by
    have hab : |a * Real.cos t| < 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one t) (abs_nonneg a)).trans_lt
        (by simpa only [mul_one] using ha)
    have hne : 1 - a * Real.cos t ≠ 0 := by
      have hh := (le_abs_self (a * Real.cos t)).trans_lt hab
      linarith
    rw [hn, hd]
    field_simp [hsn, hne]
    <;> ring
  have h := poisson_cosine_integral r hr
  simp_rw [hpoint] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact (eq_div_iff (ne_of_gt hs)).mpr (by simpa only [mul_comm] using h)

/-- The cosine resolvent at an angle has denominator the absolute sine of that angle. -/
theorem angular_cosine_integral (u : ℝ) (hu : Real.sin u ≠ 0) :
    (∫ t in 0..2 * Real.pi, 1 / (1 - Real.cos u * Real.cos t)) =
      2 * Real.pi / |Real.sin u| := by
  apply normalized_cosine_integral (Real.cos u) |Real.sin u| (abs_pos.mpr hu)
  rw [sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq u]

end SRWTightness
