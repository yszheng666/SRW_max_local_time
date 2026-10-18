import SRWTightness.CovarianceInversePerturbation
import Mathlib.Tactic.NormNum

open Matrix

namespace SRWTightness

theorem covariance_inverse_difference_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K B : Matrix ι ι ℝ) (hK : IsUnit K) (hKT : Kᵀ = K) (hBT : Bᵀ = B)
    (hJ : IsUnit (1 - B * K⁻¹ * B)) (x : ι → ℝ) :
    x ⬝ᵥ (((K - B * B)⁻¹ - K⁻¹) *ᵥ x) =
      ((B * K⁻¹) *ᵥ x) ⬝ᵥ ((1 - B * K⁻¹ * B)⁻¹ *ᵥ ((B * K⁻¹) *ᵥ x)) := by
  rw [covariance_inverse_difference_factor K B hK hKT hBT hJ]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-- The density-exponent correction is nonnegative and has a dimension-free bound.
The half-identity lower bound is an explicit hypothesis here. -/
theorem covariance_inverse_difference_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K B : Matrix ι ι ℝ) (hK : IsUnit K) (hKT : Kᵀ = K) (hBT : Bᵀ = B)
    (hJ : (1 - B * K⁻¹ * B).PosDef)
    (hlower : ∀ y : ι → ℝ, (1 / 2 : ℝ) * (∑ i, y i ^ 2) ≤
      y ⬝ᵥ ((1 - B * K⁻¹ * B) *ᵥ y)) (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ (((K - B * B)⁻¹ - K⁻¹) *ᵥ x) ∧
    x ⬝ᵥ (((K - B * B)⁻¹ - K⁻¹) *ᵥ x) ≤ 2 * ∑ i, ((B * K⁻¹) *ᵥ x) i ^ 2 := by
  rw [covariance_inverse_difference_quadratic K B hK hKT hBT hJ.isUnit]
  constructor
  · simpa only [star_trivial] using
      hJ.inv.posSemidef.dotProduct_mulVec_nonneg ((B * K⁻¹) *ᵥ x)
  · have h := inverse_quadratic_le_of_lower (1 - B * K⁻¹ * B) hJ.isUnit
      (1 / 2) (by norm_num) hlower ((B * K⁻¹) *ᵥ x)
    convert h using 1 <;> ring

end SRWTightness
