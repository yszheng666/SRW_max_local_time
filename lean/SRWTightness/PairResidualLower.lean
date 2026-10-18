import SRWTightness.PairResidualMatrix

open Matrix

namespace SRWTightness

/-- Quantitative residual coercivity, reusing the existing entrywise perturbation theorem. -/
theorem pairResidualMatrix_lower (Vz Vw c v d C : ℝ)
    (hC : 0 ≤ C) (hlarge : 4 * C ≤ d - v)
    (hz : |Vz - d| ≤ C) (hw : |Vw - d| ≤ C) (hc : |c - v| ≤ C)
    (x : Fin 2 → ℝ) :
    ((d - v) / 2) * (∑ j, x j ^ 2) ≤ x ⬝ᵥ (pairResidualMatrix Vz Vw c v *ᵥ x) := by
  apply entrywise_covariance_lower _ (Matrix.diagonal (fun _ : Fin 2 ↦ d - v))
    (d - v) C hC (pairResidualMatrix_entrywise Vz Vw c v d C hz hw hc)
  · intro y
    simp only [dotProduct, Matrix.mulVec_diagonal]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    nlinarith
  · simp only [Fintype.card_fin, Nat.cast_ofNat]
    linarith

end SRWTightness
