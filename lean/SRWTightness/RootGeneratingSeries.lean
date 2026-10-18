import SRWTightness.RootBinomialMoment
import Mathlib.Data.Nat.Choose.Sum

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- The finite binomial expansion as a nonnegative series, including the zero-count case. -/
theorem ennreal_one_add_pow_series (W : ℝ≥0∞) (n : ℕ) :
    (1 + W) ^ n = ∑' p : ℕ, W ^ p * (n.choose p : ℝ≥0∞) := by
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun p hp ↦ by
    have hnp : n < p := by
      have hh : ¬p < n + 1 := by simpa only [Finset.mem_range] using hp
      omega
    rw [Nat.choose_eq_zero_of_lt hnp, Nat.cast_zero, mul_zero])]
  rw [add_comm 1 W, add_pow]
  simp

/-- Binomial moments expand the total-root generating function without prior integrability. -/
theorem root_generating_series (μ : Measure WordMark) (L₁ C₁ L₂ C₂ : Finset Site)
    (W : ℝ≥0∞) :
    (∫⁻ Y, (1 + W) ^ (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y) ∂μ) =
      ∑' p : ℕ, W ^ p * rootBinomialMoment μ L₁ C₁ L₂ C₂ p := by
  simp_rw [ennreal_one_add_pow_series]
  rw [lintegral_tsum (fun p ↦ (measurable_of_countable _).aemeasurable)]
  congr 1
  funext p
  rw [lintegral_const_mul _ (measurable_of_countable _)]
  rfl

end SRWTightness
