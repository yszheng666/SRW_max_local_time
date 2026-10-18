import SRWTightness.GaussianDensityIntegrable
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import SRWTightness.GaussianQuadraticTiltDensity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The first-moment Gaussian density remains integrable after a nonnegative quadratic weight. -/
theorem gaussian_quadratic_weighted_integrable (x s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) :
    Integrable (fun z : ℝ ↦ z * Real.exp (-t * z ^ 2) * gaussianPDFReal x s.toNNReal z) := by
  have ha : 0 < 1 + 2 * s * t := by positivity
  let m := x / (1 + 2 * s * t)
  let v := (s / (1 + 2 * s * t)).toNNReal
  have hv : v ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (div_pos hs ha))
  have hi : Integrable (fun z : ℝ ↦ z) (gaussianReal m v) :=
    (IsGaussian.hasGaussianLaw_id (μ := gaussianReal m v)).integrable
  have hb := (gaussian_density_integrable_iff m v hv (fun z ↦ z)).mp hi
  have hh := hb.const_mul
    (Real.exp (-t * x ^ 2 / (1 + 2 * s * t)) / Real.sqrt (1 + 2 * s * t))
  apply hh.congr
  filter_upwards [] with z
  change _ = z * Real.exp (-t * z ^ 2) * gaussianPDFReal x s.toNNReal z
  rw [← mul_assoc, ← gaussian_quadratic_tilt_density x s t z hs ht]
  ring

end SRWTightness
