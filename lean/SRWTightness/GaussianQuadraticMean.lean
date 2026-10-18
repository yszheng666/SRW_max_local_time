import SRWTightness.GaussianCoordinateMoments
import Mathlib.LinearAlgebra.Matrix.Trace

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Every finite quadratic form is integrable under the actual Gaussian coordinate law. -/
theorem gaussian_quadratic_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K A : Matrix ι ι ℝ) :
    Integrable (fun x : ι → ℝ ↦ x ⬝ᵥ (A *ᵥ x)) (gaussianCoordinateLaw K) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hh := ((gaussianCoordinateLaw_coordinate_memLp_two K i).integrable_mul
    (gaussianCoordinateLaw_coordinate_memLp_two K j)).const_mul (A i j)
  simpa only [Pi.mul_apply, mul_left_comm] using hh

/-- Gaussian quadratic expectations equal the trace of the coefficient times covariance. -/
theorem gaussian_quadratic_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (A : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ∂gaussianCoordinateLaw K) = Matrix.trace (A * K) := by
  have hi (i j : ι) : Integrable (fun x : ι → ℝ ↦ A i j * (x i * x j))
      (gaussianCoordinateLaw K) :=
    ((gaussianCoordinateLaw_coordinate_memLp_two K i).integrable_mul
      (gaussianCoordinateLaw_coordinate_memLp_two K j)).const_mul (A i j)
  have he (x : ι → ℝ) : x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, A i j * (x i * x j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
  simp_rw [integral_finset_sum _ (fun j _ ↦ hi _ j), integral_const_mul,
    gaussianCoordinateLaw_product K hK]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsym := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) hK.isHermitian.eq
  have hk : K j i = K i j := by simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym
  rw [hk]

/-- The mean inverse-covariance correction under the numerator law is a trace difference. -/
theorem gaussianInverseCorrection_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hS : S.PosDef) :
    (∫ x, gaussianInverseCorrection K S x ∂gaussianCoordinateLaw S) =
      Fintype.card ι - Matrix.trace (K⁻¹ * S) := by
  rw [show gaussianInverseCorrection K S = (fun x ↦ x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x)) from rfl,
    gaussian_quadratic_mean S hS.posSemidef, Matrix.sub_mul,
    Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hS.det_pos.ne'), Matrix.trace_sub,
    Matrix.trace_one]

end SRWTightness
