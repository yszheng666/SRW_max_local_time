import SRWTightness.DiskEquilibriumWeightBound
import SRWTightness.DiskEnergyOuterTime

namespace SRWTightness

noncomputable def diskEnergyGapRatio : ℝ :=
  Real.exp (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + 4)

noncomputable def diskEnergyOuterRatio : ℝ :=
  Real.exp (diskGreenEnergyConstant / (2 / Real.pi) + 2)

noncomputable def diskGaussianMinimumRadius : ℝ :=
  max 4 (4 * diskEquilibriumWeightConstant / (2 / Real.pi))

theorem diskEnergyGapRatio_gt_four : 4 < diskEnergyGapRatio := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hE := div_pos diskGreenEnergyConstant_pos hg
  have hh := Real.add_one_le_exp (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + 4)
  unfold diskEnergyGapRatio
  linarith

theorem diskEnergyGapRatio_log_lower :
    1 + 2 * (diskGreenEnergyConstant / (2 / Real.pi)) ≤ Real.log diskEnergyGapRatio := by
  rw [diskEnergyGapRatio, Real.log_exp]
  linarith

theorem diskEnergyOuterRatio_ge_two : 2 ≤ diskEnergyOuterRatio := by
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hE := div_pos diskGreenEnergyConstant_pos hg
  have hh := Real.add_one_le_exp (diskGreenEnergyConstant / (2 / Real.pi) + 2)
  unfold diskEnergyOuterRatio
  linarith

theorem diskGaussianMinimumRadius_ge_four : 4 ≤ diskGaussianMinimumRadius := le_max_left _ _

theorem diskGaussianMinimumRadius_small_error (A : ℝ) (hA : diskGaussianMinimumRadius ≤ A) :
    diskEquilibriumWeightConstant / A ≤ (2 / Real.pi) * (1 / 4) := by
  have hA0 : 0 < A := by linarith [diskGaussianMinimumRadius_ge_four]
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hh : 4 * diskEquilibriumWeightConstant / (2 / Real.pi) ≤ A :=
    (le_max_right _ _).trans hA
  have hmul := (div_le_iff₀ hg).mp hh
  apply (div_le_iff₀ hA0).mpr
  nlinarith

/-- Fixed constants simultaneously supply radius separation, energy gaps, and small discrete error. -/
theorem diskGaussianParameterChoice (A R α : ℝ) (n : ℕ)
    (hA : diskGaussianMinimumRadius ≤ A) (hα : α ≤ 2 * (2 / Real.pi))
    (hR : diskEnergyOuterRatio * (A * diskEnergyGapRatio ^ (n - 1)) ≤ R) :
    (4 ≤ A) ∧ (2 ≤ diskEnergyGapRatio) ∧
    (∀ i : Fin n, 2 * (A * diskEnergyGapRatio ^ i.val) ≤ R) ∧
    (2 * (A * diskEnergyGapRatio ^ (n - 1)) ≤ R) ∧
    (1 + diskGreenEnergyConstant / (2 / Real.pi) + α / (2 * (2 / Real.pi)) ≤
      Real.log (R / (A * diskEnergyGapRatio ^ (n - 1)))) ∧
    (diskEquilibriumWeightConstant / A ≤ (2 / Real.pi) * (1 / 4)) := by
  have ha : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans hA
  have ha0 : 0 < A := by linarith
  have hq : 1 ≤ diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  have hrad : 0 < A * diskEnergyGapRatio ^ (n - 1) := by positivity
  have houter : 2 * (A * diskEnergyGapRatio ^ (n - 1)) ≤ R :=
    (mul_le_mul_of_nonneg_right diskEnergyOuterRatio_ge_two hrad.le).trans hR
  have hsep (i : Fin n) : 2 * (A * diskEnergyGapRatio ^ i.val) ≤ R := by
    apply le_trans _ houter
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul_of_nonneg_left _ ha0.le
    exact pow_le_pow_right₀ hq (by omega)
  have hr : diskEnergyOuterRatio ≤ R / (A * diskEnergyGapRatio ^ (n - 1)) :=
    (le_div_iff₀ hrad).mpr hR
  have hlog := Real.log_le_log (by unfold diskEnergyOuterRatio; positivity) hr
  rw [diskEnergyOuterRatio, Real.log_exp] at hlog
  have hαdiv : α / (2 * (2 / Real.pi)) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr (by simpa using hα)
  exact ⟨ha, by linarith [diskEnergyGapRatio_gt_four], hsep, houter,
    by linarith, diskGaussianMinimumRadius_small_error A hA⟩

end SRWTightness
