import SRWTightness.RootRealGeneratingBound
import SRWTightness.RootLogGeneratingError

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- Actual real exponential moments inherit the exact first-mean log coefficient. -/
theorem root_real_exponential_bound (μ : Measure WordMark) [IsProbabilityMeasure μ]
    (L₁ C₁ L₂ C₂ : Finset Site) (m R s : ℝ) (hm : 0 ≤ m) (hR : 0 ≤ R)
    (hs : 0 ≤ s) (hsmall : s ≤ 1 / 2) (hRs : R * s ≤ 1 / 4)
    (hb : ∀ p : ℕ, rootBinomialMoment μ L₁ C₁ L₂ C₂ (p + 1) ≤
      ENNReal.ofReal m * ENNReal.ofReal R ^ p) :
    Integrable (fun Y ↦ Real.exp (s *
      ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ))) μ ∧
    1 ≤ (∫ Y, Real.exp (s *
      ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)) ∂μ) ∧
    Real.log (∫ Y, Real.exp (s *
      ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)) ∂μ) ≤
        m * s + m * (2 + 8 * R) * s ^ 2 := by
  obtain ⟨hW, hquad, hlin⟩ := exp_sub_one_quadratic s hs hsmall
  have hRW : R * (Real.exp s - 1) < 1 := by
    have hh := mul_le_mul_of_nonneg_left hlin hR
    nlinarith
  have hh := root_real_generating_bound μ L₁ C₁ L₂ C₂ m R (Real.exp s - 1)
    hm hR hW hRW hb
  have hfun : (fun Y ↦ (1 + (Real.exp s - 1)) ^
      (wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y)) =
      (fun Y ↦ Real.exp (s *
        ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ))) := by
    funext Y
    rw [show 1 + (Real.exp s - 1) = Real.exp s by ring, ← Real.exp_nat_mul, mul_comm]
  rw [hfun] at hh
  have hM : 1 ≤ ∫ Y, Real.exp (s *
      ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ)) ∂μ := by
    have hi := integral_mono (integrable_const (1 : ℝ)) hh.1
      (fun Y ↦ Real.one_le_exp_iff.mpr (mul_nonneg hs (Nat.cast_nonneg _)))
    simpa using hi
  exact ⟨hh.1, hM, root_log_moment_from_generating m R s _ hm hR hs hsmall hRs
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hM) hh.2⟩

end SRWTightness
