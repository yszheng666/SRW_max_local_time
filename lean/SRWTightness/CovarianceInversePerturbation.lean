import SRWTightness.MatrixInverseQuadratic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace SRWTightness

/-- Woodbury identity for a possibly singular diagonal square root. -/
theorem covariance_sub_square_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K B : Matrix ι ι ℝ) (hK : IsUnit K) (hJ : IsUnit (1 - B * K⁻¹ * B)) :
    (K - B * B)⁻¹ = K⁻¹ + K⁻¹ * B * (1 - B * K⁻¹ * B)⁻¹ * B * K⁻¹ := by
  have hh : IsUnit (1 + 1 * (-B) * K⁻¹ * B * 1) := by
    simpa only [one_mul, mul_one, Matrix.neg_mul, ← sub_eq_add_neg] using hJ
  have he := Matrix.add_mul_mul_inv_eq_sub' K B 1 (-B) hK hh
  simpa only [mul_one, one_mul, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add, ← sub_eq_add_neg] using he

theorem covariance_sub_square_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K B : Matrix ι ι ℝ) (hK : IsUnit K) :
    (K - B * B).det = K.det * (1 - B * K⁻¹ * B).det := by
  have he := Matrix.det_add_mul B (-B) ((Matrix.isUnit_iff_isUnit_det K).mp hK)
  simpa only [Matrix.mul_neg, Matrix.neg_mul, ← sub_eq_add_neg] using he

/-- Exact inverse-difference factorization behind the Gaussian density correction. -/
theorem covariance_inverse_difference_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K B : Matrix ι ι ℝ) (hK : IsUnit K) (hKT : Kᵀ = K) (hBT : Bᵀ = B)
    (hJ : IsUnit (1 - B * K⁻¹ * B)) :
    (K - B * B)⁻¹ - K⁻¹ = (B * K⁻¹)ᵀ * (1 - B * K⁻¹ * B)⁻¹ * (B * K⁻¹) := by
  rw [covariance_sub_square_inverse K B hK hJ, add_sub_cancel_left,
    Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hKT, hBT]
  simp only [Matrix.mul_assoc]

end SRWTightness
