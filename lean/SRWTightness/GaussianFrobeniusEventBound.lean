import SRWTightness.GaussianStandardizedEntropy
import SRWTightness.MatrixEntropyFrobenius

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- A quadratic lower bound also bounds every eigenvalue of a real Hermitian matrix. -/
theorem hermitian_eigenvalue_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian) (a : ℝ)
    (hlo : ∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (G *ᵥ x)) (i : ι) :
    a ≤ hG.eigenvalues i := by
  rw [hG.eigenvalues_eq]
  have hh := hlo (ofLp (hG.eigenvectorBasis i))
  have hn : (∑ j, (hG.eigenvectorBasis i) j ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hG.eigenvectorBasis.norm_eq_one]
    norm_num
  rw [hn, mul_one] at hh
  simpa only [star_trivial, RCLike.re_to_real] using hh

/-- A spectral floor makes centered Gaussian entropy quadratic in the standardized Frobenius error. -/
theorem gaussian_entropy_le_frobenius_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (hgap : ∀ x : ι → ℝ, (1 / 2 : ℝ) * (∑ i, x i ^ 2) ≤
      x ⬝ᵥ (((CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ) *ᵥ x)) :
    (∫ x, gaussianDensityWeight K S x * Real.log (gaussianDensityWeight K S x)
      ∂gaussianCoordinateLaw K) ≤
      ‖(toLp 2 (fun ij : ι × ι ↦
        ((CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ - 1) ij.1 ij.2) :
        EuclideanSpace ℝ (ι × ι))‖ ^ 2 := by
  let G := (CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ
  have hG : G.PosDef := whitened_covariance_posDef K S hK hS
  have he := matrix_trace_logdet_frobenius_bound G hG
    (hermitian_eigenvalue_lower G hG.isHermitian (1 / 2) hgap)
  rw [gaussian_density_entropy_standardized K S hK hS]
  linarith [he.2]

/-- All measurable centered Gaussian events differ by at most twice the standardized Frobenius error. -/
theorem gaussian_frobenius_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (hgap : ∀ x : ι → ℝ, (1 / 2 : ℝ) * (∑ i, x i ^ 2) ≤
      x ⬝ᵥ (((CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ) *ᵥ x))
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    |(gaussianCoordinateLaw S).real s - (gaussianCoordinateLaw K).real s| ≤
      2 * ‖(toLp 2 (fun ij : ι × ι ↦
        ((CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ - 1) ij.1 ij.2) :
        EuclideanSpace ℝ (ι × ι))‖ := by
  have hh := Real.sqrt_le_sqrt (gaussian_entropy_le_frobenius_sq K S hK hS hgap)
  rw [Real.sqrt_sq (norm_nonneg _)] at hh
  exact (gaussian_entropy_event_bound K S hK hS s hs).trans
    (mul_le_mul_of_nonneg_left hh (by norm_num))

/-- The same centered Gaussian Frobenius comparison holds with independent auxiliary randomness. -/
theorem gaussian_frobenius_event_bound_aux {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (hgap : ∀ x : ι → ℝ, (1 / 2 : ℝ) * (∑ i, x i ^ 2) ≤
      x ⬝ᵥ (((CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ) *ᵥ x))
    (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s) :
    |((gaussianCoordinateLaw S).prod ν).real s - ((gaussianCoordinateLaw K).prod ν).real s| ≤
      2 * ‖(toLp 2 (fun ij : ι × ι ↦
        ((CFC.sqrt K)⁻¹ * S * ((CFC.sqrt K)⁻¹)ᵀ - 1) ij.1 ij.2) :
        EuclideanSpace ℝ (ι × ι))‖ := by
  have hh := gaussian_trace_entropy_event_bound_aux ν K S hK hS s hs
  rw [← gaussian_density_entropy_formula K S hK hS] at hh
  have hr := Real.sqrt_le_sqrt (gaussian_entropy_le_frobenius_sq K S hK hS hgap)
  rw [Real.sqrt_sq (norm_nonneg _)] at hr
  exact hh.trans (mul_le_mul_of_nonneg_left hr (by norm_num))

end SRWTightness
