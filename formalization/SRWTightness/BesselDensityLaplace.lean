import SRWTightness.GaussianQuadraticFirstMoment
import SRWTightness.GaussianQuadraticWeightedIntegrable
import SRWTightness.HalfLinePairIntegral
import SRWTightness.BesselThreeKernel

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The literal killed Brownian kernel is the difference of the two reflected Gaussian densities. -/
theorem killed_brownian_density_gaussian (s x y : ℝ) (hs : 0 < s) :
    killedBrownianDensity s x y =
      gaussianPDFReal x s.toNNReal y - gaussianPDFReal x s.toNNReal (-y) := by
  simp only [killedBrownianDensity, gaussianPDFReal_def, Real.coe_toNNReal s hs.le]
  have h1 : (y - x) ^ 2 = (x - y) ^ 2 := by ring
  have h2 : (-y - x) ^ 2 = (x + y) ^ 2 := by ring
  rw [h1, h2]
  ring

/-- The literal Bessel density has the exact radial Gaussian quadratic Laplace transform. -/
theorem bessel_density_quadratic_laplace (s x t : ℝ) (hs : 0 < s)
    (hx : 0 < x) (ht : 0 ≤ t) :
    (∫ y in Set.Ioi (0 : ℝ), Real.exp (-t * y ^ 2) * besselThreeDensity s x y) =
      Real.exp (-t * x ^ 2 / (1 + 2 * s * t)) / Real.sqrt (1 + 2 * s * t) ^ 3 := by
  let f : ℝ → ℝ := fun y ↦ y * Real.exp (-t * y ^ 2) * gaussianPDFReal x s.toNNReal y
  have hi : Integrable f := gaussian_quadratic_weighted_integrable x s t hs ht
  have he (y : ℝ) : Real.exp (-t * y ^ 2) * besselThreeDensity s x y =
      x⁻¹ * (f y + f (-y)) := by
    rw [besselThreeDensity, killed_brownian_density_gaussian s x y hs]
    simp only [f, neg_sq]
    ring
  simp_rw [he]
  rw [integral_const_mul, half_line_pair_integral f hi]
  have hv : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have hmean := integral_gaussianReal_eq_integral_smul
    (μ := x) (f := fun z : ℝ ↦ z * Real.exp (-t * z ^ 2)) hv
  simp only [smul_eq_mul] at hmean
  have hf : (∫ y, f y) = ∫ z : ℝ, z * Real.exp (-t * z ^ 2) ∂gaussianReal x s.toNNReal := by
    rw [hmean]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [f]
    ring
  rw [hf, gaussian_quadratic_first_moment x s t hs ht]
  have ha : 0 < 1 + 2 * s * t := by positivity
  have hroot := Real.sq_sqrt ha.le
  have hS : Real.sqrt (1 + 2 * s * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  field_simp
  nlinarith

end SRWTightness
