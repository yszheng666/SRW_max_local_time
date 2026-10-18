import SRWTightness.WhiteningMatrixBound
import SRWTightness.CenteredVectorMean

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- Covariances of finite linear observation families transform by A C A-transpose. -/
theorem covariance_matrix_linear_image {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 μ) (A : Matrix ι ι ℝ) (i j : ι) :
    covariance (fun ω ↦ ∑ r, A i r * U r ω) (fun ω ↦ ∑ s, A j s * U s ω) μ =
      (A * (Matrix.of fun r s ↦ covariance (U r) (U s) μ) * Aᵀ) i j := by
  rw [covariance_fun_sum_fun_sum (fun r ↦ (hU r).const_mul (A i r))
    (fun s ↦ (hU s).const_mul (A j s))]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Centering before a finite linear transformation leaves its covariance formula unchanged. -/
theorem covariance_centered_linear_image {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 μ) (A : Matrix ι ι ℝ) (i j : ι) :
    covariance (fun ω ↦ ∑ r, A i r * (U r ω - ∫ z, U r z ∂μ))
      (fun ω ↦ ∑ s, A j s * (U s ω - ∫ z, U s z ∂μ)) μ =
        (A * (Matrix.of fun r s ↦ covariance (U r) (U s) μ) * Aᵀ) i j := by
  have hV (i : ι) : MemLp (fun ω ↦ U i ω - ∫ z, U i z ∂μ) 2 μ :=
    (hU i).sub (memLp_const _)
  rw [covariance_matrix_linear_image μ _ hV]
  have he : (fun r s ↦ covariance (fun ω ↦ U r ω - ∫ z, U r z ∂μ)
      (fun ω ↦ U s ω - ∫ z, U s z ∂μ) μ) =
      (fun r s ↦ covariance (U r) (U s) μ) := by
    funext r s
    rw [covariance_sub_const_left ((hU r).integrable (by norm_num)),
      covariance_sub_const_right ((hU s).integrable (by norm_num))]
  rw [he]

/-- The actual centered observation vector has identity covariance after inverse-root whitening. -/
theorem whitened_observation_covariance {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ι → Ω → ℝ)
    (hU : ∀ i, MemLp (U i) 2 μ)
    (hC : Matrix.PosDef (fun i j ↦ covariance (U i) (U j) μ)) (i j : ι) :
    let C : Matrix ι ι ℝ := fun i j ↦ covariance (U i) (U j) μ
    let V : Ω → EuclideanSpace ℝ ι := fun ω ↦ toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ)
    let W := fun ω ↦ toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt C)⁻¹) (V ω)
    covariance (fun ω ↦ W ω i) (fun ω ↦ W ω j) μ = if i = j then 1 else 0 := by
  let C : Matrix ι ι ℝ := fun i j ↦ covariance (U i) (U j) μ
  have hh := covariance_centered_linear_image μ U hU ((CFC.sqrt C)⁻¹) i j
  have he : (Matrix.of fun r s ↦ covariance (U r) (U s) μ) = C := by ext r s; rfl
  rw [he, matrix_whitening_covariance C hC] at hh
  exact hh

end SRWTightness
