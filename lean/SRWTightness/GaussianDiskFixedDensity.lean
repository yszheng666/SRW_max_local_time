import SRWTightness.GaussianDiskFixedParameters
import SRWTightness.GaussianDensityRatio
import SRWTightness.BrownianCovarianceCorrection

open Matrix

namespace SRWTightness

/-- Exact density ratio and both uniform correction bounds for the full disk Gaussian vector. -/
theorem gaussian_disk_fixed_density {n : ℕ} (b : Site) (R A α : ℝ) (hn : 0 < n)
    (hA : diskPointGaussianMinimumRadius ≤ A) (hα : α ≤ 2 * (2 / Real.pi))
    (hR : diskEnergyOuterRatio * (A * diskEnergyGapRatio ^ (n - 1)) ≤ R) :
    let K := brownianTimeMatrix (geometricDiskPointTime R A diskEnergyGapRatio α n) (n + 1)
    let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) n
    let S := K - Matrix.diagonal e
    let J := diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e
    K.PosDef ∧ S.PosDef ∧
    (1 ≤ (Real.sqrt (1 - J).det)⁻¹ ∧
      (Real.sqrt (1 - J).det)⁻¹ ≤
        Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))) ∧
    ∀ x : Fin (n + 1) → ℝ,
      (gaussianCovarianceDensity S x).toReal / (gaussianCovarianceDensity K x).toReal =
        (Real.sqrt (1 - J).det)⁻¹ * Real.exp (-(x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x)) / 2) ∧
      0 ≤ x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x) ∧
      x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x) ≤ 2 * ∑ i, e i * (K⁻¹ *ᵥ x) i ^ 2 := by
  obtain ⟨ha, hq, hsep, houter, htime, _⟩ := diskGaussianParameterChoice A R α n
    (diskPointGaussianMinimumRadius_ge_base.trans hA) hα hR
  have hp : 1 ≤ diskEnergyGapRatio ^ (n - 1) := one_le_pow₀ (by linarith)
  have harad : 1 ≤ A * diskEnergyGapRatio ^ (n - 1) := by nlinarith
  have hfirst := equilibriumEnergyTime_disk_ge_one R _ α harad houter htime
  have hpoint := diskPointGaussianMinimumRadius_log_gap A hA
  have hsmall := diskPointGaussianMinimumRadius_small_error A hA
  let T := geometricDiskPointTime R A diskEnergyGapRatio α n
  let K := brownianTimeMatrix T (n + 1)
  let e := geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) n
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hT : T 0 = 0 := geometricDiskPointTime_zero R A diskEnergyGapRatio α n
  have hgap := geometricDiskPointTime_gaps R A diskEnergyGapRatio α n hn (by linarith) (by linarith)
    diskEnergyGapRatio_log_lower (fun i hi ↦ hsep ⟨i, hi⟩) hfirst hpoint
  have hK : K.PosDef := by
    dsimp [K]
    rw [brownianTimeMatrix_eq_increment T hT (n + 1)
      (fun k hk ↦ by linarith [hgap k hk])]
    exact incrementCovariance_posDef _ 1 (by norm_num) (fun i ↦ hgap i.val i.isLt)
  have hlo (x : Fin (n + 1) → ℝ) : (1 / 4 : ℝ) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x) := by
    have hh := brownianTimeMatrix_quadratic_lower T hT (n + 1) 1 (by norm_num) hgap x
    simpa only [K, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hh
  have he (i : Fin (n + 1)) : 0 ≤ e i :=
    geometricDiskPointError_nonneg b A R diskEnergyGapRatio _ hg.le n i
  have hsum : (∑ i, e i) ≤ (diskEquilibriumWeightConstant / A) / (2 / Real.pi) := by
    dsimp [e]
    rw [geometricDiskPointError_sum]
    exact equilibriumDiscreteError_geometric_sum_upper b A R diskEnergyGapRatio _ ha hq hg hsep
  have hsumSmall : (∑ i, e i) ≤ (1 / 4 : ℝ) / 2 := by
    apply hsum.trans
    apply (div_le_iff₀ hg).mpr
    nlinarith
  have hesmall (i : Fin (n + 1)) : e i ≤ (1 / 4 : ℝ) / 2 :=
    (Finset.single_le_sum (fun j _ ↦ he j) (Finset.mem_univ i)).trans hsumSmall
  have hS := smallDiagonal_covariance_posDef K hK.isHermitian (1 / 4)
    (by norm_num) hlo e hesmall
  have hJ := smallDiagonal_resolvent_posDef K hK (1 / 4) (by norm_num) hlo e he hesmall
  have hdet := smallDiagonal_determinant_bounds K hK (1 / 4) (by norm_num) hlo e he hesmall
  have hexp : (∑ i, e i) / (1 / 4) ≤
      4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)) := by
    calc
      _ ≤ ((diskEquilibriumWeightConstant / A) / (2 / Real.pi)) / (1 / 4) :=
        div_le_div_of_nonneg_right hsum (by norm_num)
      _ = _ := by ring
  refine ⟨hK, hS, ⟨hdet.1, hdet.2.trans (Real.exp_le_exp.mpr hexp)⟩, ?_⟩
  intro x
  have hsquare := diagonalSquareRoot_square e he
  have hratio := gaussianCovarianceDensity_sub_square_ratio K (diagonalSquareRoot e) hK
    (by rw [hsquare]; exact hS) hJ x
  rw [hsquare] at hratio
  refine ⟨hratio, ?_⟩
  exact brownianTimeMatrix_inverse_correction T hT (n + 1) 1 (by norm_num) hgap e he
    (fun i ↦ by convert hesmall i using 1 <;> norm_num) x

end SRWTightness
