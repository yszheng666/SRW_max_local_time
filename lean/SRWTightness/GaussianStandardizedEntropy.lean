import SRWTightness.GaussianEntropyFormula
import SRWTightness.WhiteningMatrixBound

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace SRWTightness

/-- Standardizing by a positive covariance preserves positive definiteness of the other covariance. -/
theorem whitened_covariance_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) :
    let A := (CFC.sqrt K)⁻¹
    (A * S * Aᵀ).PosDef := by
  have hu : IsUnit ((CFC.sqrt K)⁻¹) := Matrix.isUnit_nonsing_inv_iff.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (matrix_sqrt_posDef K hK).det_pos.ne'))
  have hh := hu.posDef_star_right_conjugate_iff.mpr hS
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hh

/-- The standardized covariance has the usual inverse-covariance trace. -/
theorem whitened_covariance_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) :
    let A := (CFC.sqrt K)⁻¹
    Matrix.trace (A * S * Aᵀ) = Matrix.trace (K⁻¹ * S) := by
  dsimp only
  rw [Matrix.trace_mul_cycle, Matrix.transpose_nonsing_inv, matrix_sqrt_symmetric,
    ← Matrix.mul_inv_rev, matrix_sqrt_square K hK.posSemidef]

/-- The determinant of the standardized covariance is the determinant ratio. -/
theorem whitened_covariance_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) :
    let A := (CFC.sqrt K)⁻¹
    (A * S * Aᵀ).det = S.det / K.det := by
  dsimp only
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc
    _ = ((CFC.sqrt K)⁻¹).det * ((CFC.sqrt K)⁻¹).det * S.det := by ring
    _ = (((CFC.sqrt K)⁻¹) * ((CFC.sqrt K)⁻¹)).det * S.det := by rw [Matrix.det_mul]
    _ = S.det / K.det := by
      rw [← Matrix.mul_inv_rev, matrix_sqrt_square K hK.posSemidef, Matrix.det_nonsing_inv]
      simp only [Ring.inverse_eq_inv]
      ring

/-- Centered Gaussian relative entropy is the trace/log-determinant error of the standardized covariance. -/
theorem gaussian_density_entropy_standardized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) :
    let A := (CFC.sqrt K)⁻¹
    let G := A * S * Aᵀ
    (∫ x, gaussianDensityWeight K S x * Real.log (gaussianDensityWeight K S x)
      ∂gaussianCoordinateLaw K) = (Matrix.trace G - Fintype.card ι - Real.log G.det) / 2 := by
  dsimp only
  rw [gaussian_density_entropy_formula K S hK hS, whitened_covariance_trace K S hK,
    whitened_covariance_det K S hK, Real.log_div hS.det_pos.ne' hK.det_pos.ne']
  ring

end SRWTightness
