import SRWTightness.BesselDensityLaplace

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The literal radial transition density is Lebesgue integrable. -/
theorem bessel_density_integrable (s x : ℝ) (hs : 0 < s) :
    Integrable (besselThreeDensity s x) := by
  let f : ℝ → ℝ := fun y ↦ y * gaussianPDFReal x s.toNNReal y
  have hi : Integrable f := by
    simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one] using
      gaussian_quadratic_weighted_integrable x s 0 hs le_rfl
  have hh := (hi.add hi.comp_neg).const_mul x⁻¹
  apply hh.congr
  filter_upwards [] with y
  rw [besselThreeDensity, killed_brownian_density_gaussian s x y hs]
  dsimp [f]
  ring

/-- The literal Bessel density has total mass one on the positive half-line. -/
theorem bessel_density_integral_one (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    (∫ y in Set.Ioi (0 : ℝ), besselThreeDensity s x y) = 1 := by
  simpa using bessel_density_quadratic_laplace s x 0 hs hx le_rfl

end SRWTightness
