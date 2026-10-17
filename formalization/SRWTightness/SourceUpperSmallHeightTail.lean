import SRWTightness.SourceUpperCombinedTailProbability

open MeasureTheory Set
namespace SRWTightness

/-- Extend a fine-field tail from heights at least one to all nonnegative heights. -/
theorem source_upper_small_height_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (D c h : ℝ) (hD : 0 ≤ D) (hc : 0 ≤ c) (hh : 1 ≤ h)
    (hTail : ∀ z : ℝ, 1 ≤ z →
      μ.real (Ici z) ≤ D * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / h)) :
    ∀ z : ℝ, 0 ≤ z → μ.real (Ici z) ≤
      (D + Real.exp (2 + c)) * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / h) := by
  intro z hz
  have hC : 0 ≤ D + Real.exp (2 + c) := by positivity
  by_cases hz1 : 1 ≤ z
  · exact (hTail z hz1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_nonneg _))
        (by linarith)) (Real.exp_nonneg _))
  · have hzlt : z < 1 := lt_of_not_ge hz1
    have hh0 : 0 < h := by linarith
    have hq : c * z ^ 2 / h ≤ c := by
      apply (div_le_iff₀ hh0).mpr
      have hs : z ^ 2 ≤ 1 := by nlinarith
      exact (mul_le_mul_of_nonneg_left hs hc).trans
        (by simpa using mul_le_mul_of_nonneg_left hh hc)
    have he : 1 ≤ Real.exp (2 + c) * Real.exp (-2 * z - c * z ^ 2 / h) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      linarith
    have hp : Real.exp (2 + c) ≤ (D + Real.exp (2 + c)) * (1 + z) := by
      exact (le_add_of_nonneg_left hD).trans
        (le_mul_of_one_le_right hC (by linarith))
    exact (measureReal_le_one (μ := μ) (s := Ici z)).trans
      (he.trans (mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)))

end SRWTightness
