import SRWTightness.PairResidualLower
import Mathlib.Tactic.Ring

open Matrix

namespace SRWTightness

/-- Removing the common endpoint variance gives the exact two-site residual quadratic form. -/
theorem pairResidualMatrix_quadratic (Vz Vw c v a b : ℝ) :
    (![a, b] : Fin 2 → ℝ) ⬝ᵥ (pairResidualMatrix Vz Vw c v *ᵥ ![a, b]) =
      Vz * a ^ 2 + 2 * c * a * b + Vw * b ^ 2 - v * (a + b) ^ 2 := by
  simp [dotProduct, Matrix.mulVec, pairResidualMatrix, Fin.sum_univ_two]
  ring

/-- For residual time at least two, the actual residual controls both site coefficients. -/
theorem pairResidualMatrix_unit_lower (Vz Vw c v d C : ℝ)
    (hC : 0 ≤ C) (hlarge : 4 * C ≤ d - v) (htwo : 2 ≤ d - v)
    (hz : |Vz - d| ≤ C) (hw : |Vw - d| ≤ C) (hc : |c - v| ≤ C) (a b : ℝ) :
    a ^ 2 + b ^ 2 ≤ Vz * a ^ 2 + 2 * c * a * b + Vw * b ^ 2 - v * (a + b) ^ 2 := by
  have hh := pairResidualMatrix_lower Vz Vw c v d C hC hlarge hz hw hc ![a, b]
  rw [pairResidualMatrix_quadratic] at hh
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hh
  have hs : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith

end SRWTightness
