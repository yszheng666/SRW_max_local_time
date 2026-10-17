import SRWTightness.SourcePairNodeResidual

namespace SRWTightness

/-- One logarithmic margin supplies both residual separation and small total diagonal correction. -/
noncomputable def sourcePairLogMargin : ℝ :=
  max (4 * sourcePairResidualError + 3)
    (Real.log (max 1 (16 * diskEquilibriumWeightConstant / (2 / Real.pi))) -
      sourceEquilibriumTimeError - sourceLowerTimeError)

theorem source_pair_radius_margin (A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A)
    (hlog : sourcePairLogMargin + sourceEquilibriumTimeError + sourceLowerTimeError ≤
      Real.log A) :
    (4 * sourcePairResidualError + 3 + sourceEquilibriumTimeError +
      sourceLowerTimeError ≤ Real.log A) ∧
    (diskEquilibriumWeightConstant / A) / (2 / Real.pi) ≤ 1 / 16 := by
  have hfirst : 4 * sourcePairResidualError + 3 ≤ sourcePairLogMargin := le_max_left _ _
  have hsecond : Real.log (max 1 (16 * diskEquilibriumWeightConstant / (2 / Real.pi))) -
      sourceEquilibriumTimeError - sourceLowerTimeError ≤ sourcePairLogMargin := le_max_right _ _
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hApos : 0 < A := by linarith
  have hMpos : 0 < max (1 : ℝ) (16 * diskEquilibriumWeightConstant / (2 / Real.pi)) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlogs : Real.log (max 1 (16 * diskEquilibriumWeightConstant / (2 / Real.pi))) ≤
      Real.log A := by linarith
  have hM : max 1 (16 * diskEquilibriumWeightConstant / (2 / Real.pi)) ≤ A :=
    (Real.log_le_log_iff hMpos hApos).mp hlogs
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hr := (le_max_right (1 : ℝ) (16 * diskEquilibriumWeightConstant / (2 / Real.pi))).trans hM
  have hm := (div_le_iff₀ hg).mp hr
  constructor
  · linarith
  · apply (div_le_iff₀ hg).mpr
    apply (div_le_iff₀ hApos).mpr
    nlinarith

end SRWTightness
