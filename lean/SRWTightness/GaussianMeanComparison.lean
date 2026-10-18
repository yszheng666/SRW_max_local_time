import SRWTightness.GaussianMeanEvent
import SRWTightness.GaussianTranslation
import SRWTightness.WhiteningMatrixBound

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- The square root of mean-shift entropy is controlled by the whitened mean norm. -/
theorem gaussian_mean_entropy_sqrt_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Real.sqrt ((m ⬝ᵥ (K⁻¹ *ᵥ m)) / 2) ≤
      ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 m)‖ := by
  have he : m ⬝ᵥ (K⁻¹ *ᵥ m) =
      ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 m)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa only [ofLp_toEuclideanCLM, ofLp_toLp] using
      (matrix_sqrt_inverse_energy K hK m).symm
  rw [he]
  calc
    _ ≤ Real.sqrt (‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 m)‖ ^ 2) :=
      Real.sqrt_le_sqrt (by
        have h := sq_nonneg ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 m)‖
        linarith)
    _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- Two arbitrary Gaussian means are compared in the reference covariance norm. -/
theorem gaussian_mean_difference_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m n : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    |(gaussianMeanCoordinateLaw m K).real s - (gaussianMeanCoordinateLaw n K).real s| ≤
      2 * ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 (m - n))‖ := by
  have hm : Measurable (fun x : ι → ℝ ↦ n + x) := by fun_prop
  have hh := gaussian_mean_event_bound (m - n) K hK ((fun x ↦ n + x) ⁻¹' s) (hm hs)
  have he : n + (m - n) = m := by abel
  rw [← map_measureReal_apply hm hs,
    gaussianMeanCoordinateLaw_map_add, he, ← gaussianMeanCoordinateLaw_real n K s hs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (gaussian_mean_entropy_sqrt_le (m - n) K hK)
    (by norm_num))

/-- Arbitrary mean comparison persists with independent auxiliary randomness. -/
theorem gaussian_mean_difference_event_bound_aux {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (m n : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef)
    (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s) :
    |((gaussianMeanCoordinateLaw m K).prod ν).real s -
      ((gaussianMeanCoordinateLaw n K).prod ν).real s| ≤
      2 * ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 (m - n))‖ := by
  have hm : Measurable (fun x : (ι → ℝ) × Ξ ↦ (n + x.1, x.2)) := by fun_prop
  have hh := gaussian_mean_event_bound_aux ν (m - n) K hK
    ((fun x ↦ (n + x.1, x.2)) ⁻¹' s) (hm hs)
  have he : n + (m - n) = m := by abel
  rw [← gaussianMeanCoordinateLaw_prod_add_real ν (m - n) n K s hs, he,
    ← gaussianMeanCoordinateLaw_prod_real ν n K s hs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (gaussian_mean_entropy_sqrt_le (m - n) K hK)
    (by norm_num))

/-- Centered covariance comparison and mean comparison combine without changing the reference norm. -/
theorem gaussian_mean_covariance_event_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m n : ι → ℝ) (K S : Matrix ι ι ℝ) (hK : K.PosDef) (δ : ℝ)
    (hcov : ∀ s : Set (ι → ℝ), MeasurableSet s →
      |(gaussianCoordinateLaw S).real s - (gaussianCoordinateLaw K).real s| ≤ δ)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    |(gaussianMeanCoordinateLaw m S).real s - (gaussianMeanCoordinateLaw n K).real s| ≤
      δ + 2 * ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 (m - n))‖ := by
  have hc := hcov ((fun x ↦ m + x) ⁻¹' s) ((show Measurable (fun x : ι → ℝ ↦ m + x) by fun_prop) hs)
  rw [← gaussianMeanCoordinateLaw_real m S s hs, ← gaussianMeanCoordinateLaw_real m K s hs] at hc
  exact (abs_sub_le _ ((gaussianMeanCoordinateLaw m K).real s) _).trans
    (add_le_add hc (gaussian_mean_difference_event_bound m n K hK s hs))

/-- The combined mean and covariance comparison also permits independent auxiliary randomness. -/
theorem gaussian_mean_covariance_event_bound_aux {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (m n : ι → ℝ) (K S : Matrix ι ι ℝ) (hK : K.PosDef) (δ : ℝ)
    (hcov : ∀ s : Set ((ι → ℝ) × Ξ), MeasurableSet s →
      |((gaussianCoordinateLaw S).prod ν).real s - ((gaussianCoordinateLaw K).prod ν).real s| ≤ δ)
    (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s) :
    |((gaussianMeanCoordinateLaw m S).prod ν).real s -
      ((gaussianMeanCoordinateLaw n K).prod ν).real s| ≤
      δ + 2 * ‖toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt K)⁻¹) (toLp 2 (m - n))‖ := by
  have hc := hcov ((fun x ↦ (m + x.1, x.2)) ⁻¹' s)
    ((show Measurable (fun x : (ι → ℝ) × Ξ ↦ (m + x.1, x.2)) by fun_prop) hs)
  rw [← gaussianMeanCoordinateLaw_prod_real ν m S s hs,
    ← gaussianMeanCoordinateLaw_prod_real ν m K s hs] at hc
  exact (abs_sub_le _ (((gaussianMeanCoordinateLaw m K).prod ν).real s) _).trans
    (add_le_add hc (gaussian_mean_difference_event_bound_aux ν m n K hK s hs))

end SRWTightness
