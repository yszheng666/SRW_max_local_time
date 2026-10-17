import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Matrix

namespace SRWTightness

/-- An elementary inverse quadratic-form bound, avoiding a dimension-dependent norm estimate. -/
theorem inverse_quadratic_le_of_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsUnit A) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x)) (y : ι → ℝ) :
    y ⬝ᵥ (A⁻¹ *ᵥ y) ≤ (∑ i, y i ^ 2) / c := by
  let z := A⁻¹ *ᵥ y
  have hz : A *ᵥ z = y := by
    dsimp [z]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.one_mulVec]
  have hl := hlower z
  rw [hz] at hl
  have hZ : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hY : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hq : 0 ≤ z ⬝ᵥ y := (mul_nonneg hc.le hZ).trans hl
  have hcs : (z ⬝ᵥ y) ^ 2 ≤ (∑ i, z i ^ 2) * ∑ i, y i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z y
  have hmul := mul_le_mul_of_nonneg_left hcs hc.le
  have hlmul := mul_le_mul_of_nonneg_right hl hY
  have hb : c * (z ⬝ᵥ y) ≤ ∑ i, y i ^ 2 := by
    by_cases he : z ⬝ᵥ y = 0
    · rw [he, mul_zero]; exact hY
    · have hp : 0 < z ⬝ᵥ y := lt_of_le_of_ne hq (Ne.symm he)
      nlinarith
  change y ⬝ᵥ z ≤ _
  rw [dotProduct_comm]
  apply (le_div_iff₀ hc).mpr
  nlinarith

end SRWTightness
