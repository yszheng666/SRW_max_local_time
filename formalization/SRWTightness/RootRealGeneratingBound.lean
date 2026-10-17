import SRWTightness.RootRealIntegralTransfer

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- The real geometric bound has exactly the nonnegative extended-real representation. -/
theorem root_generating_bound_ofReal (m R W : ℝ) (hm : 0 ≤ m) (hR : 0 ≤ R)
    (hW : 0 ≤ W) (hRW : R * W < 1) :
    ENNReal.ofReal (1 + m * W / (1 - R * W)) =
      1 + ENNReal.ofReal m * ENNReal.ofReal W /
        (1 - ENNReal.ofReal R * ENNReal.ofReal W) := by
  have hd : 0 < 1 - R * W := by linarith
  rw [ENNReal.ofReal_add (by norm_num) (div_nonneg (mul_nonneg hm hW) hd.le),
    ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_mul hm,
    ENNReal.ofReal_sub 1 (mul_nonneg hR hW), ENNReal.ofReal_mul hR]
  simp

/-- Actual real generating moments are integrable and satisfy the geometric bound. -/
theorem root_real_generating_bound (μ : Measure WordMark) [IsProbabilityMeasure μ]
    (L₁ C₁ L₂ C₂ : Finset Site) (m R W : ℝ) (hm : 0 ≤ m) (hR : 0 ≤ R)
    (hW : 0 ≤ W) (hRW : R * W < 1)
    (hb : ∀ p : ℕ, rootBinomialMoment μ L₁ C₁ L₂ C₂ (p + 1) ≤
      ENNReal.ofReal m * ENNReal.ofReal R ^ p) :
    Integrable (fun Y ↦ (1 + W) ^
      (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y)) μ ∧
    (∫ Y, (1 + W) ^ (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y) ∂μ) ≤
      1 + m * W / (1 - R * W) := by
  have hd : 0 < 1 - R * W := by linarith
  apply wordMark_real_integral_of_bound μ _ _
    (by have hh := div_nonneg (mul_nonneg hm hW) hd.le; linarith)
    (fun Y ↦ pow_nonneg (by linarith) _)
  simp_rw [wordMark_generating_ofReal L₁ C₁ L₂ C₂ W hW]
  rw [root_generating_bound_ofReal m R W hm hR hW hRW]
  exact root_generating_bound μ L₁ C₁ L₂ C₂ _ _ _ hb

end SRWTightness
