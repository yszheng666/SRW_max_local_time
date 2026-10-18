import SRWTightness.FiniteOccupationRowInputs
import Mathlib.Analysis.Normed.Group.Constructions

open Matrix

namespace SRWTightness

/-- A uniform absolute row sum bounds multiplication in the finite supremum norm. -/
theorem matrix_row_mulVec_norm_bound (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (q : ℝ) (hq : 0 ≤ q) (hrow : ∀ i, ∑ j, |M i j| ≤ q)
    (v : ι → ℝ) : ‖M.mulVec v‖ ≤ q * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg v))).mpr
  intro i
  change ‖∑ j, M i j * v j‖ ≤ _
  calc
    _ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
    _ = ∑ j, |M i j| * ‖v j‖ := by simp only [norm_mul, Real.norm_eq_abs]
    _ ≤ ∑ j, |M i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ q * ‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg v)

/-- A strict row contraction makes one minus the matrix invertible, including empty dimensions. -/
theorem matrix_row_contraction_isUnit (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, |M i j| ≤ q) : IsUnit (1 - M) := by
  have hker (v : ι → ℝ) (hv : (1 - M).mulVec v = 0) : v = 0 := by
    have he : v = M.mulVec v := by
      apply sub_eq_zero.mp
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hv
    have hb := matrix_row_mulVec_norm_bound ι M q hq hrow v
    rw [← he] at hb
    have hn : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp hn
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w he
  have hz : (1 - M).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, he, sub_self]
  exact sub_eq_zero.mp (hker (v - w) hz)

/-- The complete finite resolvent row bound follows internally from the supremum norm estimate. -/
theorem finite_resolvent_row_bound_input_internal : FiniteResolventRowBoundInput := by
  intro ι _ _ M q hq hq1 hrow i
  let v : ι → ℝ := ((1 - M)⁻¹.mulVec 1)
  have hu := matrix_row_contraction_isUnit ι M q hq hq1 hrow
  have he : (1 - M).mulVec v = 1 := by
    dsimp [v]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mulVec]
  have hf : v = 1 + M.mulVec v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at he
    exact sub_eq_iff_eq_add.mp he
  have hone : ‖(1 : ι → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by intro j; simp)
  have hb : ‖v‖ ≤ 1 + q * ‖v‖ := by
    calc
      _ = ‖1 + M.mulVec v‖ := congrArg norm hf
      _ ≤ ‖(1 : ι → ℝ)‖ + ‖M.mulVec v‖ := norm_add_le _ _
      _ ≤ 1 + q * ‖v‖ := add_le_add hone (matrix_row_mulVec_norm_bound ι M q hq hrow v)
  have hn : ‖v‖ ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
    nlinarith
  exact (show |v i| ≤ ‖v‖ from by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i).trans hn

end SRWTightness
