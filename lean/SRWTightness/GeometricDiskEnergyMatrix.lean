import SRWTightness.GeometricDiskEnergyTimes
import SRWTightness.MatrixQuadraticReindex
import Mathlib.Data.Fin.Rev

open Matrix

namespace SRWTightness

noncomputable def geometricDiskEnergyMatrix (R A q α : ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := .of fun i j ↦
  min (equilibriumEnergyTime (diskFinset R) (diskFinset (A * q ^ i.val)) α (2 / Real.pi))
    (equilibriumEnergyTime (diskFinset R) (diskFinset (A * q ^ j.val)) α (2 / Real.pi))

theorem geometricDiskEnergyMatrix_eq_reindex (R A q α : ℝ) (n : ℕ) :
    geometricDiskEnergyMatrix R A q α n =
      (brownianTimeMatrix (geometricDiskEnergyTime R A q α n) n).submatrix
        Fin.revPerm Fin.revPerm := by
  have he (i : Fin n) : n - (i.rev.val + 1) = i.val := by
    rw [Fin.val_rev]
    omega
  ext i j
  simp only [geometricDiskEnergyMatrix, Matrix.of_apply, Matrix.submatrix_apply,
    brownianTimeMatrix, Fin.revPerm_apply, geometricDiskEnergyTime, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ↓reduceIte, he]

/-- The actual disk-energy covariance has a dimension-independent lower bound. -/
theorem geometricDiskEnergyMatrix_lower (R A q α : ℝ) (n : ℕ) (hA : 1 ≤ A) (hq : 1 ≤ q)
    (hlog : 1 + 2 * (diskGreenEnergyConstant / (2 / Real.pi)) ≤ Real.log q)
    (hsep : ∀ i < n, 2 * (A * q ^ i) ≤ R)
    (hfirst : 1 ≤ equilibriumEnergyTime (diskFinset R)
      (diskFinset (A * q ^ (n - 1))) α (2 / Real.pi)) :
    (geometricDiskEnergyMatrix R A q α n).PosDef ∧
      ∀ x : Fin n → ℝ, (1 / 4 : ℝ) * (∑ i, x i ^ 2) ≤
        x ⬝ᵥ (geometricDiskEnergyMatrix R A q α n *ᵥ x) := by
  let T := geometricDiskEnergyTime R A q α n
  have hT : T 0 = 0 := geometricDiskEnergyTime_zero R A q α n
  have hgap := geometricDiskEnergyTime_gaps R A q α n hA hq hlog hsep hfirst
  have hK : (brownianTimeMatrix T n).PosDef := by
    rw [brownianTimeMatrix_eq_increment T hT n (fun k hk ↦ by linarith [hgap k hk])]
    exact incrementCovariance_posDef _ 1 (by norm_num) (fun i ↦ hgap i.val i.isLt)
  have hlo (x : Fin n → ℝ) : (1 / 4 : ℝ) * (∑ i, x i ^ 2) ≤
      x ⬝ᵥ (brownianTimeMatrix T n *ᵥ x) := by
    have hh := brownianTimeMatrix_quadratic_lower T hT n 1 (by norm_num) hgap x
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hh
  rw [geometricDiskEnergyMatrix_eq_reindex]
  exact ⟨hK.submatrix Fin.revPerm.injective,
    matrix_quadratic_lower_reindex _ Fin.revPerm _ hlo⟩

end SRWTightness
