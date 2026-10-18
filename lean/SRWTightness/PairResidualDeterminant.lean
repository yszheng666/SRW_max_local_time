import SRWTightness.PairResidualMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace SRWTightness

/-- The two-site residual determinant grows quadratically in the remaining time. -/
theorem pairResidualMatrix_det_lower (Vz Vw c v d C : ℝ)
    (hC : 0 ≤ C) (hd : 0 < d - v) (hlarge : 4 * C ≤ d - v)
    (hz : |Vz - d| ≤ C) (hw : |Vw - d| ≤ C) (hc : |c - v| ≤ C) :
    (d - v) ^ 2 / 4 ≤ (pairResidualMatrix Vz Vw c v).det := by
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨hw1, hw2⟩ := abs_le.mp hw
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hp := mul_le_mul
    (show d - v - C ≤ Vz - v by linarith)
    (show d - v - C ≤ Vw - v by linarith)
    (show 0 ≤ d - v - C by linarith)
    (show 0 ≤ Vz - v by linarith)
  have hs : (c - v) ^ 2 ≤ C ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hlarge hd.le
  rw [Matrix.det_fin_two]
  simp only [pairResidualMatrix]
  norm_num
  nlinarith [sq_nonneg (d - v)]

end SRWTightness
