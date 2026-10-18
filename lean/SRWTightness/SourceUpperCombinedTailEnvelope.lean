import SRWTightness.SourceUpperResidualAbsorption

namespace SRWTightness

/-- A nonnegative residual shift retains half the fine-field quadratic decay. -/
theorem source_upper_shifted_fine_tail (z u h c : ℝ) (hu : 0 ≤ u) (huz : u ≤ z)
    (hh : 0 < h) (hc : 0 ≤ c) :
    (1 + (z - u)) * Real.exp (-2 * (z - u) - c * (z - u) ^ 2 / h) ≤
      (1 + z) * Real.exp (-2 * z - c * z ^ 2 / (2 * h)) *
        Real.exp (2 * u + c * u ^ 2 / h) := by
  have hs : z ^ 2 / 2 - u ^ 2 ≤ (z - u) ^ 2 := by
    nlinarith [sq_nonneg (z - 2 * u)]
  have ht := mul_le_mul_of_nonneg_left hs (div_nonneg hc hh.le)
  have he : -2 * (z - u) - c * (z - u) ^ 2 / h ≤
      (-2 * z - c * z ^ 2 / (2 * h)) + (2 * u + c * u ^ 2 / h) := by
    field_simp at ht ⊢
    nlinarith
  calc
    _ ≤ (1 + z) * Real.exp
        ((-2 * z - c * z ^ 2 / (2 * h)) + (2 * u + c * u ^ 2 / h)) :=
      mul_le_mul (by linarith) (Real.exp_le_exp.mpr he) (Real.exp_nonneg _)
        (by linarith)
    _ = _ := by rw [Real.exp_add]; ring

/-- A Gaussian residual tail absorbs the linear exponential at a fixed constant cost. -/
theorem source_upper_gaussian_residual_envelope (z b c h : ℝ)
    (hz : 0 ≤ z) (hb : 0 < b) (hh : 0 < h) (hch : c / h ≤ b / 2) :
    Real.exp (-b * z ^ 2) ≤
      Real.exp (2 / b) * ((1 + z) * Real.exp (-2 * z - c * z ^ 2 / h)) := by
  have hs : 2 * z ≤ b / 2 * z ^ 2 + 2 / b := by
    apply (mul_le_mul_iff_right₀ hb).mp
    field_simp
    nlinarith [sq_nonneg (b * z - 2)]
  have hc := mul_le_mul_of_nonneg_right hch (sq_nonneg z)
  have hc' : c * z ^ 2 / h ≤ b / 2 * z ^ 2 := by
    calc
      c * z ^ 2 / h = c / h * z ^ 2 := by ring
      _ ≤ b / 2 * z ^ 2 := hc
  have he : -b * z ^ 2 ≤ 2 / b + (-2 * z - c * z ^ 2 / h) := by
    nlinarith only [hs, hc']
  calc
    _ ≤ Real.exp (2 / b + (-2 * z - c * z ^ 2 / h)) := Real.exp_le_exp.mpr he
    _ = Real.exp (2 / b) * Real.exp (-2 * z - c * z ^ 2 / h) := Real.exp_add _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact le_mul_of_one_le_left (Real.exp_nonneg _) (by linarith)

end SRWTightness
