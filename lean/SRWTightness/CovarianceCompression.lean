import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Abel

open Matrix

namespace SRWTightness

/-- Covariance of the harmonic remainder under compression of a precision matrix. -/
theorem covariance_compression_remainder {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (G Q : Matrix n n ℝ) (B : Matrix m m ℝ)
    (M : Matrix m n ℝ) (hQ : Qᵀ = Q) (hB : Bᵀ = B)
    (hMM : M * Mᵀ = 1) (hQG : Q * G = 1) (hBC : B * (M * Q * Mᵀ) = 1) :
    (M - B * M * Q) * G * (M - B * M * Q)ᵀ = M * G * Mᵀ - B := by
  have hGQ : G * Q = 1 := mul_eq_one_comm.mp hQG
  have hBM : B * M * Q * Mᵀ = 1 := by simpa only [Matrix.mul_assoc] using hBC
  have h1 : M * G * (Q * (Mᵀ * B)) = B := by
    calc
      _ = M * (G * Q) * Mᵀ * B := by simp only [Matrix.mul_assoc]
      _ = M * Mᵀ * B := by rw [hGQ, Matrix.mul_one]
      _ = B := by rw [hMM, Matrix.one_mul]
  have h2 : B * M * Q * G * Mᵀ = B := by
    calc
      _ = B * (M * (Q * G) * Mᵀ) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hQG, Matrix.mul_one, hMM, Matrix.mul_one]
  have h3 : B * M * Q * G * (Q * (Mᵀ * B)) = B := by
    calc
      _ = (B * M * Q * Mᵀ) * B := by simp only [Matrix.mul_assoc, hQG, Matrix.one_mul]
      _ = B := by rw [hBM, Matrix.one_mul]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, hQ, hB,
    Matrix.sub_mul, Matrix.mul_sub, h1, h2, h3]
  abel

end SRWTightness
