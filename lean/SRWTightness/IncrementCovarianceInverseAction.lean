import SRWTightness.IncrementCovarianceAction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

namespace SRWTightness

/-- The first covariance row is the first time gap times the full suffix sum. -/
theorem incrementCovariance_mulVec_zero {n : ℕ} (d x : Fin (n + 1) → ℝ) :
    (incrementCovariance d *ᵥ x) 0 = d 0 * suffixSum x 0 := by
  rw [incrementCovariance_mulVec]
  simp

/-- The inverse covariance vector reconstructs the observation vector under positive time gaps. -/
theorem incrementCovariance_inverse_action {n : ℕ} (d y : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hd : ∀ i, δ ≤ d i) :
    incrementCovariance d *ᵥ ((incrementCovariance d)⁻¹ *ᵥ y) = y := by
  have hu := (incrementCovariance_posDef d δ hδ hd).isUnit
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mulVec]

/-- The first normalized observation equals the inverse vector's initial suffix sum. -/
theorem incrementCovariance_inverse_suffix_zero {n : ℕ} (d y : Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hd : ∀ i, δ ≤ d i) :
    suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) 0 = y 0 / d 0 := by
  have hh := incrementCovariance_mulVec_zero d ((incrementCovariance d)⁻¹ *ᵥ y)
  rw [incrementCovariance_inverse_action d y δ hδ hd] at hh
  apply (eq_div_iff (ne_of_gt (hδ.trans_le (hd 0)))).mpr
  simpa only [mul_comm] using hh.symm

/-- Every later normalized observation increment equals the corresponding inverse-vector suffix sum. -/
theorem incrementCovariance_inverse_suffix_step {n : ℕ} (d y : Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hd : ∀ i, δ ≤ d i) (i : Fin n) :
    suffixSum ((incrementCovariance d)⁻¹ *ᵥ y) i.succ.val =
      (y i.succ - y i.castSucc) / d i.succ := by
  have hh := incrementCovariance_mulVec_step d ((incrementCovariance d)⁻¹ *ᵥ y) i
  rw [incrementCovariance_inverse_action d y δ hδ hd] at hh
  apply (eq_div_iff (ne_of_gt (hδ.trans_le (hd i.succ)))).mpr
  simpa only [mul_comm] using hh.symm

end SRWTightness
