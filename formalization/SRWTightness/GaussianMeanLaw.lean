import SRWTightness.GaussianCoordinateMoments
import SRWTightness.DensityPushforward

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

noncomputable def gaussianMeanCoordinateLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (gaussianCoordinateLaw K).map (fun x ↦ m + x)

/-- The translated coordinate construction is the actual multivariate Gaussian with that mean. -/
theorem gaussianMeanCoordinateLaw_eq_multivariate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) :
    gaussianMeanCoordinateLaw m K =
      (multivariateGaussian (toLp 2 m) K).map (fun x : EuclideanSpace ℝ ι ↦ ofLp x) := by
  unfold gaussianMeanCoordinateLaw gaussianCoordinateLaw multivariateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  ext i
  simp

/-- The actual Gaussian law with a mean remains a probability measure. -/
theorem gaussianMeanCoordinateLaw_isProbabilityMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) : IsProbabilityMeasure (gaussianMeanCoordinateLaw m K) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  unfold gaussianMeanCoordinateLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Every coordinate has the specified Gaussian mean. -/
theorem gaussianMeanCoordinateLaw_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (i : ι) :
    (∫ x : ι → ℝ, x i ∂gaussianMeanCoordinateLaw m K) = m i := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  unfold gaussianMeanCoordinateLaw
  rw [integral_map (φ := fun x : ι → ℝ ↦ m + x) (f := fun x : ι → ℝ ↦ x i)
    (by fun_prop) (measurable_pi_apply i).aestronglyMeasurable]
  change (∫ x : ι → ℝ, m i + x i ∂gaussianCoordinateLaw K) = m i
  rw [integral_add (integrable_const _) ((gaussianCoordinateLaw_coordinate_memLp_two K i).integrable (by norm_num))]
  simp [gaussianCoordinateLaw_mean]

/-- Translating the actual Gaussian law translates its Lebesgue density. -/
theorem gaussianMeanCoordinateLaw_density {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    gaussianMeanCoordinateLaw m K =
      volume.withDensity (fun x ↦ gaussianCovarianceDensity K (x - m)) := by
  unfold gaussianMeanCoordinateLaw gaussianCoordinateLaw
  rw [multivariateGaussian_coordinate_density K hK,
    density_pushforward_add volume m (gaussianCovarianceDensity K)
      (gaussianCovarianceDensity_measurable K)]
  congr 1
  funext x
  rw [sub_eq_add_neg, add_comm x (-m)]

end SRWTightness
