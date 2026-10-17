import SRWTightness.ExternalSubGaussianMoment
import SRWTightness.SourceUpperCombinedTailIntegral

open MeasureTheory Set
namespace SRWTightness

/-- The residual exponential moment is uniform in height and in all sufficiently large scales. -/
theorem source_upper_residual_compact_moment (hMoment : SubGaussianPositiveMomentInput)
    (A b : ℝ) (hA : 0 < A) (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∀ u : ℝ, 0 ≤ u → ν.real (Ici u) ≤ A * Real.exp (-b * u ^ 2)) →
      ∀ z h c : ℝ, c / h ≤ b / 2 →
        (∫ u in Icc 0 z, Real.exp (2 * u + c * u ^ 2 / h) ∂ν) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := hMoment A b hA hb
  refine ⟨M, hM, ?_⟩
  intro ν _ hTail z h c hch
  obtain ⟨hi, hm⟩ := hbound ν hTail
  have hc : (∫ u in Icc 0 z, Real.exp (2 * u + c * u ^ 2 / h) ∂ν) ≤
      ∫ u in Icc 0 z, Real.exp (2 * max u 0 + b / 2 * (max u 0) ^ 2) ∂ν := by
    apply setIntegral_mono_on
      (show Continuous (fun u : ℝ ↦ Real.exp (2 * u + c * u ^ 2 / h)) by
        fun_prop).continuousOn.integrableOn_Icc hi.integrableOn measurableSet_Icc
    intro u hu
    rw [max_eq_left hu.1]
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right hch (sq_nonneg u)
    have he : c * u ^ 2 / h = c / h * u ^ 2 := by ring
    rw [he]
    linarith only [ht]
  exact hc.trans ((setIntegral_le_integral hi
    (Filter.Eventually.of_forall fun u ↦ Real.exp_nonneg _)).trans hm)

/-- The fine-field shifted convolution has the uniform source decay after moment control. -/
theorem source_upper_shifted_fine_tail_bound (hMoment : SubGaussianPositiveMomentInput)
    (A b : ℝ) (hA : 0 < A) (hb : 0 < b) :
    ∃ M : ℝ, 0 < M ∧ ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∀ u : ℝ, 0 ≤ u → ν.real (Ici u) ≤ A * Real.exp (-b * u ^ 2)) →
      ∀ z h c : ℝ, 0 ≤ z → 0 < h → 0 ≤ c → c / h ≤ b / 2 →
        (∫ u in Icc 0 z, (1 + (z - u)) *
          Real.exp (-2 * (z - u) - c * (z - u) ^ 2 / h) ∂ν) ≤
          M * ((1 + z) * Real.exp (-2 * z - c * z ^ 2 / (2 * h))) := by
  obtain ⟨M, hM, hm⟩ := source_upper_residual_compact_moment hMoment A b hA hb
  refine ⟨M, hM, ?_⟩
  intro ν _ hTail z h c hz hh hc hch
  have ht := mul_le_mul_of_nonneg_left (hm ν hTail z h c hch)
    (show 0 ≤ (1 + z) * Real.exp (-2 * z - c * z ^ 2 / (2 * h)) by positivity)
  exact (source_upper_shifted_fine_tail_integral ν z h c hh hc).trans
    (by simpa only [mul_comm M] using ht)

end SRWTightness
