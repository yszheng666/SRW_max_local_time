import SRWTightness.SourceScaleThreshold
import SRWTightness.GeometricTerminalIndex
import SRWTightness.SourceReferenceIntensity
import SRWTightness.DiskPointParameterChoice

namespace SRWTightness

noncomputable def sourceGaussianThreshold (A : ℝ) : ℝ :=
  max (sourceScaleThreshold A) diskEnergyOuterRatio

/-- The actual source radii and reference intensity satisfy the complete Gaussian comparison input. -/
theorem source_gaussian_parameters (t A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A)
    (ht : sourceGaussianThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      sourceReferenceIntensity (sourceLowerRadius t) 14 ≤ 2 * (2 / Real.pi) ∧
      diskEnergyOuterRatio * (A * diskEnergyGapRatio ^ I) ≤
        Real.exp 1 * sourceLowerRadius t + 14 := by
  have ha : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hA0 : 0 < A := by linarith
  have htbase : sourceScaleThreshold A ≤ t := (le_max_left _ _).trans ht
  have htS : diskEnergyOuterRatio ≤ t := (le_max_right _ _).trans ht
  obtain ⟨ht2, hcut, hm70, _⟩ := sourceScaleThreshold_conditions t A ha htbase
  have ht0 : 0 < t := by linarith
  have hm0 := sourceLowerRadius_pos t
  have hq : 1 < diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  let I := geometricTerminalIndex A diskEnergyGapRatio (sourceLowerRadius t / t ^ 6)
    hA0 hq hcut
  have hlast := (geometricTerminalIndex_spec A diskEnergyGapRatio _ hA0 hq hcut).1
  have hlastmul := (le_div_iff₀ (by positivity : 0 < t ^ 6)).mp hlast
  have ht6 : t ≤ t ^ 6 := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ t) (by norm_num : 1 ≤ 6)
  have harad : 0 ≤ A * diskEnergyGapRatio ^ I := by positivity
  have hsmall : diskEnergyOuterRatio * (A * diskEnergyGapRatio ^ I) ≤ sourceLowerRadius t := by
    have hh := mul_le_mul_of_nonneg_right (htS.trans ht6) harad
    nlinarith
  have hR : sourceLowerRadius t ≤ Real.exp 1 * sourceLowerRadius t + 14 := by
    nlinarith [Real.exp_one_gt_two]
  have hα := sourceReferenceIntensity_bounds (sourceLowerRadius t) 14 hm0
    (by norm_num) (by linarith)
  exact ⟨I, geometricTerminalIndex_max_iff A diskEnergyGapRatio _ hA0 hq hcut,
    hα.2, hsmall.trans hR⟩

end SRWTightness
