import SRWTightness.GaussianDensityRatio
import SRWTightness.SmallDiagonalDeterminant

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

/-- Quantitative density comparison under an explicitly small diagonal perturbation. -/
theorem gaussian_diagonal_density_ratio_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2)
    (hS : (K - Matrix.diagonal e).PosDef) (x : ι → ℝ) :
    (gaussianCovarianceDensity (K - Matrix.diagonal e) x).toReal /
      (gaussianCovarianceDensity K x).toReal ≤ Real.exp ((∑ i, e i) / c) := by
  let B := diagonalSquareRoot e
  have hJ := smallDiagonal_resolvent_posDef K hK c hc hlo e he hesmall
  have hJT := smallDiagonal_resolvent_lower K hK.isUnit c hc hlo e he hesmall
  have hKT : Kᵀ = K := by
    ext i j
    have hh := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) hK.isHermitian.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using hh
  have hq := covariance_diagonal_inverse_difference_bounds K e he hK.isUnit hKT hJ hJT x
  have hSS : (K - B * B).PosDef := by
    dsimp [B]
    rwa [diagonalSquareRoot_square e he]
  have hr := gaussianCovarianceDensity_sub_square_ratio K B hK hSS hJ x
  have hd := smallDiagonal_determinant_bounds K hK c hc hlo e he hesmall
  dsimp [B] at hr
  rw [diagonalSquareRoot_square e he] at hr
  rw [hr]
  have hexp : Real.exp (-(x ⬝ᵥ (((K - Matrix.diagonal e)⁻¹ - K⁻¹) *ᵥ x)) / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith [hq.1]
  exact (mul_le_of_le_one_right (inv_nonneg.mpr (Real.sqrt_nonneg _)) hexp).trans hd.2

theorem gaussian_diagonal_density_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2)
    (hS : (K - Matrix.diagonal e).PosDef) (x : ι → ℝ) :
    gaussianCovarianceDensity (K - Matrix.diagonal e) x ≤
      ENNReal.ofReal (Real.exp ((∑ i, e i) / c)) * gaussianCovarianceDensity K x := by
  have hr := gaussian_diagonal_density_ratio_upper K hK c hc hlo e he hesmall hS x
  have hp := gaussianCovarianceDensity_toReal_pos K hK x
  have hs := gaussianCovarianceDensity_toReal_pos (K - Matrix.diagonal e) hS x
  have hh := (div_le_iff₀ hp).mp hr
  have hkn := (ENNReal.toReal_pos_iff.mp hp).2
  have hsn := (ENNReal.toReal_pos_iff.mp hs).2
  have heqK := ENNReal.ofReal_toReal hkn.ne
  have heqS := ENNReal.ofReal_toReal hsn.ne
  rw [← heqS, ← heqK, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hh

theorem gaussian_diagonal_measure_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2)
    (hS : (K - Matrix.diagonal e).PosDef) :
    (multivariateGaussian 0 (K - Matrix.diagonal e)).map
        (fun φ : EuclideanSpace ℝ ι ↦ fun i ↦ φ i) ≤
      ENNReal.ofReal (Real.exp ((∑ i, e i) / c)) •
        (multivariateGaussian 0 K).map (fun φ : EuclideanSpace ℝ ι ↦ fun i ↦ φ i) := by
  rw [multivariateGaussian_coordinate_density _ hS, multivariateGaussian_coordinate_density K hK,
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (gaussian_diagonal_density_upper K hK c hc hlo e he hesmall hS)

theorem gaussian_diagonal_measure_upper_aux {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β] (ν : Measure β) [SFinite ν]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2)
    (hS : (K - Matrix.diagonal e).PosDef) :
    ((multivariateGaussian 0 (K - Matrix.diagonal e)).map
        (fun φ : EuclideanSpace ℝ ι ↦ fun i ↦ φ i)).prod ν ≤
      ENNReal.ofReal (Real.exp ((∑ i, e i) / c)) •
        (((multivariateGaussian 0 K).map
          (fun φ : EuclideanSpace ℝ ι ↦ fun i ↦ φ i)).prod ν) := by
  have hh := Measure.prod_mono
    (gaussian_diagonal_measure_upper K hK c hc hlo e he hesmall hS) (le_refl ν)
  rwa [Measure.prod_smul_left] at hh

end SRWTightness
