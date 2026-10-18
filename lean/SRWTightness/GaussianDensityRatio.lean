import SRWTightness.GaussianCovarianceDensity
import SRWTightness.CovarianceInversePerturbation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Matrix

namespace SRWTightness

/-- Exact ratio of densities already identified with actual multivariate Gaussian laws. -/
theorem gaussianCovarianceDensity_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) (x : ι → ℝ) :
    (gaussianCovarianceDensity S x).toReal / (gaussianCovarianceDensity K x).toReal =
      (Real.sqrt K.det / Real.sqrt S.det) *
        Real.exp (-(x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x)) / 2) := by
  rw [gaussianCovarianceDensity_toReal S hS, gaussianCovarianceDensity_toReal K hK,
    Matrix.sub_mulVec, dotProduct_sub]
  have hc : ((Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι) ≠ 0 := by positivity
  have hk : Real.sqrt K.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hK.det_pos)
  have hs : Real.sqrt S.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS.det_pos)
  have he : Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x) - x ⬝ᵥ (K⁻¹ *ᵥ x)) / 2) =
      Real.exp (-(x ⬝ᵥ (S⁻¹ *ᵥ x)) / 2) / Real.exp (-(x ⬝ᵥ (K⁻¹ *ᵥ x)) / 2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he]
  field_simp

/-- Determinant form of the Gaussian ratio for a square covariance correction. -/
theorem gaussianCovarianceDensity_sub_square_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K B : Matrix ι ι ℝ) (hK : K.PosDef) (hS : (K - B * B).PosDef)
    (hJ : (1 - B * K⁻¹ * B).PosDef) (x : ι → ℝ) :
    (gaussianCovarianceDensity (K - B * B) x).toReal /
      (gaussianCovarianceDensity K x).toReal =
      (Real.sqrt (1 - B * K⁻¹ * B).det)⁻¹ *
        Real.exp (-(x ⬝ᵥ (((K - B * B)⁻¹ - K⁻¹) *ᵥ x)) / 2) := by
  rw [gaussianCovarianceDensity_ratio K (K - B * B) hK hS,
    covariance_sub_square_det K B hK.isUnit, Real.sqrt_mul hK.det_pos.le]
  have hk : Real.sqrt K.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hK.det_pos)
  have hj : Real.sqrt (1 - B * K⁻¹ * B).det ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hJ.det_pos)
  congr 1
  field_simp

end SRWTightness
