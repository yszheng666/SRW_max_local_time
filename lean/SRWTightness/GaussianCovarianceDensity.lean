import SRWTightness.GaussianLinearDensity
import SRWTightness.GaussianCovarianceSquareRoot

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal MatrixOrder

namespace SRWTightness

noncomputable def gaussianCovarianceDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (abs (CFC.sqrt G).det⁻¹) *
    ∏ i, gaussianPDF 0 1 (((CFC.sqrt G)⁻¹ *ᵥ x) i)

/-- Density of the actual multivariate Gaussian after exposing its real coordinates. -/
theorem multivariateGaussian_coordinate_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    (multivariateGaussian 0 G).map (fun φ : EuclideanSpace ℝ ι ↦ fun i ↦ φ i) =
      volume.withDensity (gaussianCovarianceDensity G) := by
  rw [multivariateGaussian_zero_pi, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun φ : EuclideanSpace ℝ ι ↦ fun i ↦ φ i) ∘
      (fun x : ι → ℝ ↦ toLp 2 ((CFC.sqrt G).mulVec x)) =
      (fun x ↦ (CFC.sqrt G) *ᵥ x) := by
    funext x
    rfl
  rw [he]
  exact gaussianPi_matrix_density (CFC.sqrt G) (matrix_sqrt_posDef G hG).isUnit

theorem gaussianCovarianceDensity_toReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (x : ι → ℝ) :
    (gaussianCovarianceDensity G x).toReal =
      (Real.sqrt G.det)⁻¹ * ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι) *
        Real.exp (-(x ⬝ᵥ (G⁻¹ *ᵥ x)) / 2) := by
  rw [gaussianCovarianceDensity, gaussianPi_matrix_density_toReal,
    matrix_sqrt_inverse_energy G hG, matrix_sqrt_det G hG,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]

theorem gaussianCovarianceDensity_toReal_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef) (x : ι → ℝ) :
    0 < (gaussianCovarianceDensity G x).toReal := by
  rw [gaussianCovarianceDensity_toReal G hG]
  have hd := hG.det_pos
  positivity

end SRWTightness
