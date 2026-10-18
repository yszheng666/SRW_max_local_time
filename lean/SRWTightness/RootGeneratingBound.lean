import SRWTightness.RootGeneratingSeries
import Mathlib.Analysis.SpecificLimits.Basic

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- Factorial bounds give the nonnegative geometric generating-function bound. -/
theorem root_generating_bound (μ : Measure WordMark) [IsProbabilityMeasure μ]
    (L₁ C₁ L₂ C₂ : Finset Site) (m R W : ℝ≥0∞)
    (hm : ∀ p : ℕ, rootBinomialMoment μ L₁ C₁ L₂ C₂ (p + 1) ≤ m * R ^ p) :
    (∫⁻ Y, (1 + W) ^ (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y) ∂μ) ≤
      1 + m * W / (1 - R * W) := by
  rw [root_generating_series, tsum_eq_zero_add' ENNReal.summable,
    pow_zero, one_mul, rootBinomialMoment_zero]
  have hs : (∑' p : ℕ, W ^ (p + 1) * rootBinomialMoment μ L₁ C₁ L₂ C₂ (p + 1)) ≤
      ∑' p : ℕ, (m * W) * (R * W) ^ p := by
    apply ENNReal.tsum_le_tsum
    intro p
    calc
      _ ≤ W ^ (p + 1) * (m * R ^ p) := mul_le_mul_left' (hm p) _
      _ = (m * W) * (R * W) ^ p := by rw [pow_succ, mul_pow]; ac_rfl
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric] at hs
  simpa only [div_eq_mul_inv] using add_le_add (le_refl (1 : ℝ≥0∞)) hs

/-- Finiteness follows from the generating bound, not from an assumed exponential moment. -/
theorem root_generating_finite (μ : Measure WordMark) [IsProbabilityMeasure μ]
    (L₁ C₁ L₂ C₂ : Finset Site) (m R W : ℝ≥0∞)
    (hm : ∀ p : ℕ, rootBinomialMoment μ L₁ C₁ L₂ C₂ (p + 1) ≤ m * R ^ p)
    (hmfin : m ≠ ∞) (hWfin : W ≠ ∞) (hRW : R * W < 1) :
    (∫⁻ Y, (1 + W) ^ (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y) ∂μ) < ∞ := by
  apply (root_generating_bound μ L₁ C₁ L₂ C₂ m R W hm).trans_lt
  finiteness [(tsub_pos_iff_lt.mpr hRW).ne']

end SRWTightness
