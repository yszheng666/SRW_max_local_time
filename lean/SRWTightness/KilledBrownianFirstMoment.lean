import SRWTightness.BesselKilledDensityTransform

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The killed Brownian law is supported on strictly positive positions. -/
theorem killed_brownian_density_law_positive (s x : ℝ) :
    ∀ᵐ y ∂killedBrownianDensityLaw s x, 0 < y := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

/-- The endpoint is integrable under the killed Brownian transition law. -/
theorem killed_brownian_endpoint_integrable (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    Integrable (fun y ↦ y) (killedBrownianDensityLaw s x) := by
  have hm : Measurable (fun y ↦ ENNReal.ofReal (killedBrownianDensity s x y)) := by
    unfold killedBrownianDensity
    fun_prop
  rw [killedBrownianDensityLaw, integrable_withDensity_iff_integrable_smul' hm
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply ((bessel_density_integrable s x hs).integrableOn.const_mul x).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (killedBrownianDensity_pos s x y hs hx hy).le, smul_eq_mul]
  unfold besselThreeDensity
  field_simp
  <;> ring

/-- Killing Brownian motion at zero preserves its first moment. -/
theorem killed_brownian_first_moment (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    (∫ y, y ∂killedBrownianDensityLaw s x) = x := by
  rw [killed_brownian_density_law_integral s x hs hx]
  have he (y : ℝ) : killedBrownianDensity s x y * y = x * besselThreeDensity s x y := by
    unfold besselThreeDensity
    field_simp
    <;> ring
  simp_rw [he]
  rw [integral_const_mul, bessel_density_integral_one s x hs hx, mul_one]

/-- Linear endpoint weighting turns every killed-kernel integral into a Bessel-kernel integral. -/
theorem killed_bessel_weighted_integral (s x : ℝ) (hs : 0 < s) (hx : 0 < x) (f : ℝ → ℝ) :
    (∫ y, (y / x) * f y ∂killedBrownianDensityLaw s x) =
      ∫ y, f y ∂besselDensityLaw s x := by
  rw [killed_brownian_density_law_integral s x hs hx,
    bessel_density_law_integral s x hs hx]
  apply integral_congr_ae
  exact ae_of_all _ (fun y ↦ by unfold besselThreeDensity; ring)

end SRWTightness
