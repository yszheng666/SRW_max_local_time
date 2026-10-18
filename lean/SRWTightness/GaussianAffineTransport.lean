import SRWTightness.GaussianMeanLaw
import SRWTightness.AuxiliaryEventComparison

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- The actual coordinate Gaussian is the square-root image of independent standard normals. -/
theorem gaussianCoordinateLaw_eq_sqrt_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) :
    gaussianCoordinateLaw K =
      (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map (fun x ↦ (CFC.sqrt K) *ᵥ x) := by
  unfold gaussianCoordinateLaw
  rw [multivariateGaussian_zero_pi, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Identity covariance is exactly the independent standard coordinate Gaussian law. -/
theorem gaussianCoordinateLaw_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    gaussianCoordinateLaw (1 : Matrix ι ι ℝ) = Measure.pi (fun _ : ι ↦ gaussianReal 0 1) := by
  rw [gaussianCoordinateLaw_eq_sqrt_map]
  simp

/-- The affine square-root image of the standard Gaussian has the required mean and covariance. -/
theorem gaussianMeanCoordinateLaw_eq_affine_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) :
    gaussianMeanCoordinateLaw m K = (gaussianCoordinateLaw (1 : Matrix ι ι ℝ)).map
      (fun x ↦ m + (CFC.sqrt K) *ᵥ x) := by
  unfold gaussianMeanCoordinateLaw
  rw [gaussianCoordinateLaw_eq_sqrt_map K, gaussianCoordinateLaw_one,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A standard convex-event approximation transports to the actual Gaussian mean and covariance. -/
theorem convex_gaussian_affine_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (δ : ℝ)
    (happrox : ∀ s : Set (ι → ℝ), MeasurableSet s → Convex ℝ s →
      |μ.real s - (gaussianCoordinateLaw (1 : Matrix ι ι ℝ)).real s| ≤ δ)
    (m : ι → ℝ) (K : Matrix ι ι ℝ)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) (hc : Convex ℝ s) :
    |(μ.map (fun x ↦ m + (CFC.sqrt K) *ᵥ x)).real s -
      (gaussianMeanCoordinateLaw m K).real s| ≤ δ := by
  have hm : Measurable (fun x : ι → ℝ ↦ m + (CFC.sqrt K) *ᵥ x) := by fun_prop
  rw [gaussianMeanCoordinateLaw_eq_affine_map, map_measureReal_apply hm hs,
    map_measureReal_apply hm hs]
  apply happrox _ (hm hs)
  exact (hc.translate_preimage_right m).linear_preimage (Matrix.toLin' (CFC.sqrt K))

end SRWTightness
