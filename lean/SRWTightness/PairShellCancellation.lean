import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- An additive logarithmic radius error gives the inverse-square exponential scale. -/
theorem pair_shell_exp_scale (a h E : ℝ) (ha : 0 < a) (he : |h - Real.log a| ≤ E) :
    Real.exp (-2 * h) ≤ Real.exp (2 * E) / a ^ 2 := by
  have hlog : Real.exp (2 * Real.log a) = a ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log ha]
    ring
  calc
    _ ≤ Real.exp (2 * E - 2 * Real.log a) :=
      Real.exp_le_exp.mpr (by linarith [(abs_le.mp he).1])
    _ = _ := by rw [Real.exp_sub, hlog]

/-- The shell covering inequalities transfer an inverse distance square to its shell radius. -/
theorem pair_shell_inverse_square (a ρ B : ℝ) (ha : 0 < a) (hρ : 0 < ρ)
    (hB : 0 ≤ B) (hcover : a ≤ B * ρ) :
    1 / ρ ^ 2 ≤ B ^ 2 / a ^ 2 := by
  apply (div_le_div_iff₀ (sq_pos_of_pos hρ) (sq_pos_of_pos ha)).mpr
  have hh := mul_self_le_mul_self ha.le hcover
  nlinarith

/-- The spatial factor in a shell count cancels the inverse spatial factor in its probability. -/
theorem pair_shell_sum_cancel {ι : Type*} (S : Finset ι) (P : ι → ℝ)
    (R a K L W : ℝ) (hR : 0 < R) (ha : 0 < a) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hcard : (S.card : ℝ) ≤ K * R ^ 2 * a ^ 2)
    (hpoint : ∀ p ∈ S, P p ≤ L / (R ^ 2 * a ^ 2) * W) :
    (∑ p ∈ S, P p) ≤ K * L * W := by
  have hden : 0 < R ^ 2 * a ^ 2 := mul_pos (sq_pos_of_pos hR) (sq_pos_of_pos ha)
  calc
    _ ≤ ∑ _p ∈ S, L / (R ^ 2 * a ^ 2) * W := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (L / (R ^ 2 * a ^ 2) * W) := by simp
    _ ≤ (K * R ^ 2 * a ^ 2) * (L / (R ^ 2 * a ^ 2) * W) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (div_nonneg hL hden.le) hW)
    _ = _ := by field_simp; <;> ring

end SRWTightness
