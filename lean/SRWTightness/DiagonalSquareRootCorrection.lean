import SRWTightness.CovarianceQuadraticCorrection
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Matrix

namespace SRWTightness

noncomputable def diagonalSquareRoot {ι : Type*} [DecidableEq ι] (e : ι → ℝ) :
    Matrix ι ι ℝ := Matrix.diagonal (fun i ↦ Real.sqrt (e i))

theorem diagonalSquareRoot_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) :
    diagonalSquareRoot e * diagonalSquareRoot e = Matrix.diagonal e := by
  rw [diagonalSquareRoot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (he i)

theorem diagonalSquareRoot_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e x : ι → ℝ) (he : ∀ i, 0 ≤ e i) :
    (∑ i, (diagonalSquareRoot e *ᵥ x) i ^ 2) = ∑ i, e i * x i ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [diagonalSquareRoot, Matrix.mulVec_diagonal, mul_pow, Real.sq_sqrt (he i)]

theorem covariance_diagonal_inverse_difference_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (hK : IsUnit K) (hKT : Kᵀ = K)
    (hJ : (1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).PosDef)
    (hlower : ∀ y : ι → ℝ, (1 / 2 : ℝ) * (∑ i, y i ^ 2) ≤
      y ⬝ᵥ ((1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e) *ᵥ y))
    (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ (((K - Matrix.diagonal e)⁻¹ - K⁻¹) *ᵥ x) ∧
    x ⬝ᵥ (((K - Matrix.diagonal e)⁻¹ - K⁻¹) *ᵥ x) ≤
      2 * ∑ i, e i * (K⁻¹ *ᵥ x) i ^ 2 := by
  have h := covariance_inverse_difference_bounds K (diagonalSquareRoot e) hK hKT
    (Matrix.diagonal_transpose _) hJ hlower x
  rw [diagonalSquareRoot_square e he, ← Matrix.mulVec_mulVec,
    diagonalSquareRoot_energy e (K⁻¹ *ᵥ x) he] at h
  exact h

end SRWTightness
