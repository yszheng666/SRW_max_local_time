import SRWTightness.EntrywiseCovariancePerturbation
import SRWTightness.WhiteningMatrixBound

open Matrix
open scoped MatrixOrder

namespace SRWTightness

/-- Small entrywise covariance errors preserve half the reference quadratic form. -/
theorem covariance_relative_lower_from_entries {ι : Type*} [Fintype ι]
    (K S : Matrix ι ι ℝ) (a ε : ℝ) (hε : 0 ≤ ε)
    (hlo : ∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (hentry : ∀ i j, |S i j - K i j| ≤ ε)
    (hsmall : ε * Fintype.card ι ≤ a / 2) (x : ι → ℝ) :
    (1 / 2 : ℝ) * (x ⬝ᵥ (K *ᵥ x)) ≤ x ⬝ᵥ (S *ᵥ x) := by
  have hh := (abs_le.mp (entrywise_quadratic_error S K ε hε hentry x)).1
  have hs := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ ∑ i, x i ^ 2 from Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i)))
  have hk := hlo x
  nlinarith

/-- The relative quadratic lower bound becomes an identity lower bound after whitening. -/
theorem whitened_covariance_lower_from_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (a ε : ℝ) (hε : 0 ≤ ε)
    (hlo : ∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (hentry : ∀ i j, |S i j - K i j| ≤ ε)
    (hsmall : ε * Fintype.card ι ≤ a / 2) (x : ι → ℝ) :
    (1 / 2 : ℝ) * (∑ i, x i ^ 2) ≤
      x ⬝ᵥ (((CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ) *ᵥ x) := by
  let A := (CFC.sqrt K)⁻¹
  have hAT : Aᵀ = A := by
    dsimp only [A]
    rw [Matrix.transpose_nonsing_inv, matrix_sqrt_symmetric]
  have hh := covariance_relative_lower_from_entries K S a ε hε hlo hentry hsmall (A *ᵥ x)
  rw [matrix_whitening_energy K hK] at hh
  have he : x ⬝ᵥ ((A * S * Aᵀ) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (S *ᵥ (A *ᵥ x)) := by
    have hd := Matrix.dotProduct_transpose_mulVec Aᵀ x (S *ᵥ (Aᵀ *ᵥ x))
    simpa only [Matrix.transpose_transpose, Matrix.mulVec_mulVec, hAT, Matrix.mul_assoc]
      using hd.trans (dotProduct_comm _ _)
  rw [he]
  exact hh

end SRWTightness
