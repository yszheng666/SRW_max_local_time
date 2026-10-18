import SRWTightness.GaussianPiRepresentation
import Mathlib.Analysis.Matrix.PosDef

open Matrix
open scoped MatrixOrder

namespace SRWTightness

theorem matrix_sqrt_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) : (CFC.sqrt G).PosDef := by
  apply (CFC.sqrt_nonneg G).posSemidef.posDef_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro he
  have hh := congrArg Matrix.det (matrix_sqrt_square G hG.posSemidef)
  rw [Matrix.det_mul, he, zero_mul] at hh
  exact (ne_of_gt hG.det_pos) hh.symm

theorem matrix_sqrt_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) : (CFC.sqrt G).det = Real.sqrt G.det := by
  have hh := congrArg Matrix.det (matrix_sqrt_square G hG.posSemidef)
  rw [Matrix.det_mul, ← pow_two] at hh
  rw [← hh, Real.sqrt_sq (matrix_sqrt_posDef G hG).det_pos.le]

theorem matrix_sqrt_inverse_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (x : ι → ℝ) :
    (∑ i, ((CFC.sqrt G)⁻¹ *ᵥ x) i ^ 2) = x ⬝ᵥ (G⁻¹ *ᵥ x) := by
  have hh := Matrix.dotProduct_transpose_mulVec (CFC.sqrt G)⁻¹ x ((CFC.sqrt G)⁻¹ *ᵥ x)
  rw [Matrix.transpose_nonsing_inv, matrix_sqrt_symmetric, Matrix.mulVec_mulVec,
    ← Matrix.mul_inv_rev, matrix_sqrt_square G hG.posSemidef] at hh
  simpa only [dotProduct, pow_two] using hh.symm

end SRWTightness
