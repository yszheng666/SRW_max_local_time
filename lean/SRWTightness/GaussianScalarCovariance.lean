import SRWTightness.GaussianConvolution

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace
namespace SRWTightness

/-- Scalar normalization of a centered Gaussian scales its actual covariance quadratically. -/
theorem multivariateGaussian_zero_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (c : ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map (fun φ ↦ c • φ) =
      multivariateGaussian (0 : EuclideanSpace ℝ ι) (c ^ 2 • S) := by
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_map_smul, charFun_multivariateGaussian hS,
    charFun_multivariateGaussian (hS.smul (sq_nonneg c))]
  have he : (c • x) ⬝ᵥ S *ᵥ (c • x) = x ⬝ᵥ (c ^ 2 • S) *ᵥ x := by
    change (c • (x : ι → ℝ)) ⬝ᵥ S *ᵥ (c • (x : ι → ℝ)) =
      (x : ι → ℝ) ⬝ᵥ (c ^ 2 • S) *ᵥ (x : ι → ℝ)
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_mulVec, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  simp only [WithLp.ofLp_smul] at he ⊢
  simp only [inner_zero_right, he]

/-- The scalar normalization map preserves the Gaussian laws with the exact scaled covariance. -/
theorem gaussian_scalar_covariance_preserving {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (hS : S.PosSemidef) (c : ℝ) :
    MeasurePreserving (fun φ : EuclideanSpace ℝ ι ↦ c • φ)
      (multivariateGaussian 0 S) (multivariateGaussian 0 (c ^ 2 • S)) :=
  ⟨by fun_prop, multivariateGaussian_zero_smul S hS c⟩

end SRWTightness
