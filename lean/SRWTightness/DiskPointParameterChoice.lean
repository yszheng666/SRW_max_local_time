import SRWTightness.DiskGaussianParameterChoice
import SRWTightness.DiskPointEnergyGap

namespace SRWTightness

noncomputable def diskPointGaussianMinimumRadius : ℝ :=
  max diskGaussianMinimumRadius
    (max (8 * diskEquilibriumWeightConstant / (2 / Real.pi))
      (Real.exp (1 + diskPointEnergyGapConstant)))

theorem diskPointGaussianMinimumRadius_ge_base :
    diskGaussianMinimumRadius ≤ diskPointGaussianMinimumRadius := le_max_left _ _

theorem diskPointGaussianMinimumRadius_small_error (A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) :
    diskEquilibriumWeightConstant / A ≤ (2 / Real.pi) / 8 := by
  have ha := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have ha0 : 0 < A := by linarith
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hh : 8 * diskEquilibriumWeightConstant / (2 / Real.pi) ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hA)
  have hmul := (div_le_iff₀ hg).mp hh
  apply (div_le_iff₀ ha0).mpr
  nlinarith

theorem diskPointGaussianMinimumRadius_log_gap (A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) :
    1 + diskPointEnergyGapConstant ≤ Real.log A := by
  have hh : Real.exp (1 + diskPointEnergyGapConstant) ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hA)
  have hl := Real.log_le_log (Real.exp_pos _) hh
  rwa [Real.log_exp] at hl

end SRWTightness
