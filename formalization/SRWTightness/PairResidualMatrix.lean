import SRWTightness.EntrywiseCovariancePerturbation
import Mathlib.Tactic.FinCases

open Matrix

namespace SRWTightness

/-- Residual covariance after removing the common Brownian endpoint. -/
def pairResidualMatrix (Vz Vw c v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j ↦ if i = j then (if i = 0 then Vz else Vw) - v else c - v

theorem pairResidualMatrix_entrywise (Vz Vw c v d C : ℝ)
    (hz : |Vz - d| ≤ C) (hw : |Vw - d| ≤ C) (hc : |c - v| ≤ C) :
    ∀ i j, |pairResidualMatrix Vz Vw c v i j -
      Matrix.diagonal (fun _ : Fin 2 ↦ d - v) i j| ≤ C := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pairResidualMatrix, Matrix.diagonal_apply] <;> first
    | simpa only [sub_sub_sub_cancel_right] using hz
    | simpa only [sub_sub_sub_cancel_right] using hw
    | exact hc

theorem pairResidualMatrix_posDef (Vz Vw c v d C : ℝ)
    (hC : 0 ≤ C) (hd : 0 < d - v) (hlarge : 4 * C ≤ d - v)
    (hz : |Vz - d| ≤ C) (hw : |Vw - d| ≤ C) (hc : |c - v| ≤ C) :
    (pairResidualMatrix Vz Vw c v).PosDef := by
  have hsym : (pairResidualMatrix Vz Vw c v).IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairResidualMatrix, Matrix.conjTranspose_apply]
  apply entrywise_covariance_posDef _ (Matrix.diagonal (fun _ : Fin 2 ↦ d - v))
    hsym (d - v) C hd hC (pairResidualMatrix_entrywise Vz Vw c v d C hz hw hc)
  · intro x
    simp only [dotProduct, Matrix.mulVec_diagonal]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    nlinarith
  · simp only [Fintype.card_fin, Nat.cast_ofNat]
    linarith

end SRWTightness
