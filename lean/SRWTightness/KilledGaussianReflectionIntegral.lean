import SRWTightness.GaussianReflectionDensity
import SRWTightness.HalfLineReflectionIntegral
import SRWTightness.BesselThreeKernel

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The endpoint reflection weight is the literal killed kernel in distance coordinates. -/
theorem killed_gaussian_reflection_density (s x b : ℝ) (hs : 0 < s) :
    gaussianPDFReal 0 s.toNNReal b * (1 - Real.exp (-(2 * x * (x - b) / s))) =
      killedBrownianDensity s x (x - b) := by
  rw [mul_sub, mul_one, gaussian_reflection_density s x b hs]
  simp only [gaussianPDFReal_def, Real.coe_toNNReal s hs.le, sub_zero,
    killedBrownianDensity]
  have h1 : x - (x - b) = b := by ring
  have h2 : x + (x - b) = 2 * x - b := by ring
  rw [h1, h2]
  ring

/-- Integrating reflected endpoint weights in distance coordinates gives the killed kernel. -/
theorem killed_gaussian_reflection_integral (s x : ℝ) (hs : 0 < s) (f : ℝ → ℝ) :
    (∫ b in Set.Iio x, gaussianPDFReal 0 s.toNNReal b *
      (1 - Real.exp (-(2 * x * (x - b) / s))) * f (x - b)) =
      ∫ y in Set.Ioi (0 : ℝ), killedBrownianDensity s x y * f y := by
  simp_rw [killed_gaussian_reflection_density s x _ hs]
  have he := half_line_reflection_integral (fun y ↦ killedBrownianDensity s x y * f y) x x
  simpa only [sub_self] using he

end SRWTightness
