import SRWTightness.GaussianGeometricDiskUpper
import SRWTightness.GeometricDiskEnergyMatrix
import SRWTightness.DiskEnergyOuterTime

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Gaussian comparison for the actual disk-energy matrix, with all matrix lower-bound and
weight hypotheses replaced by explicit radius conditions. -/
theorem gaussian_disk_energy_comparison {n : ℕ} {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsFiniteMeasure ν] (b : Site) (R A q α : ℝ)
    (hA : 4 ≤ A) (hq : 2 ≤ q)
    (hlog : 1 + 2 * (diskGreenEnergyConstant / (2 / Real.pi)) ≤ Real.log q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R)
    (houter : 2 * (A * q ^ (n - 1)) ≤ R)
    (htime : 1 + diskGreenEnergyConstant / (2 / Real.pi) + α / (2 * (2 / Real.pi)) ≤
      Real.log (R / (A * q ^ (n - 1))))
    (hsmall : diskEquilibriumWeightConstant / A ≤ (2 / Real.pi) * (1 / 4)) :
    let K := geometricDiskEnergyMatrix R A q α n
    let e : Fin n → ℝ := fun i ↦ equilibriumDiscreteError
      (translateFinset b (diskFinset R)) (translateFinset b (diskFinset (A * q ^ i.val)))
      (2 / Real.pi)
    (K - Matrix.diagonal e).PosDef ∧
      (gaussianCoordinateLaw (K - Matrix.diagonal e)).prod ν ≤
        ENNReal.ofReal (Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))) •
          ((gaussianCoordinateLaw K).prod ν) := by
  have hq1 : 1 ≤ q := by linarith
  have hp : 1 ≤ q ^ (n - 1) := one_le_pow₀ hq1
  have ha : 1 ≤ A * q ^ (n - 1) := by nlinarith
  have hf := equilibriumEnergyTime_disk_ge_one R (A * q ^ (n - 1)) α ha houter htime
  have hK := geometricDiskEnergyMatrix_lower R A q α n (by linarith) hq1 hlog
    (fun i hi ↦ hsep ⟨i, hi⟩) hf
  have hh := gaussian_disk_geometric_error_upper ν b A R q (2 / Real.pi) hA hq
    (by positivity) hsep (geometricDiskEnergyMatrix R A q α n) hK.1
    (1 / 4) (by norm_num) hK.2 hsmall
  have he : (diskEquilibriumWeightConstant / A) / ((2 / Real.pi) * (1 / 4)) =
      4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)) := by ring
  rw [he] at hh
  exact hh

end SRWTightness
