import SRWTightness.GaussianQuadraticIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Coordinate means of the actual centered Gaussian law vanish. -/
theorem gaussianCoordinateLaw_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (i : ι) :
    (∫ x : ι → ℝ, x i ∂gaussianCoordinateLaw K) = 0 := by
  unfold gaussianCoordinateLaw
  rw [integral_map (φ := fun φ : EuclideanSpace ℝ ι ↦ fun j ↦ φ j)
    (f := fun x : ι → ℝ ↦ x i) (by fun_prop) (measurable_pi_apply i).aestronglyMeasurable]
  change (∫ x : EuclideanSpace ℝ ι, x i ∂multivariateGaussian 0 K) = 0
  have hh := (innerSL ℝ (EuclideanSpace.basisFun ι ℝ i)).integral_comp_comm
    (IsGaussian.integrable_fun_id (μ := multivariateGaussian 0 K))
  simpa [PiLp.inner_apply] using hh

/-- The covariance entries of the actual Gaussian coordinate law equal its matrix parameter. -/
theorem gaussianCoordinateLaw_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (i j : ι) :
    covariance (fun x : ι → ℝ ↦ x i) (fun x ↦ x j) (gaussianCoordinateLaw K) = K i j := by
  unfold gaussianCoordinateLaw
  rw [covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable (by fun_prop)]
  exact covariance_eval_multivariateGaussian hK i j

/-- Centered Gaussian coordinate products have exactly the prescribed second moments. -/
theorem gaussianCoordinateLaw_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosSemidef) (i j : ι) :
    (∫ x : ι → ℝ, x i * x j ∂gaussianCoordinateLaw K) = K i j := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have hh := gaussianCoordinateLaw_covariance K hK i j
  rw [covariance_eq_sub (gaussianCoordinateLaw_coordinate_memLp_two K i)
    (gaussianCoordinateLaw_coordinate_memLp_two K j), gaussianCoordinateLaw_mean,
    gaussianCoordinateLaw_mean, zero_mul, sub_zero] at hh
  exact hh

end SRWTightness
