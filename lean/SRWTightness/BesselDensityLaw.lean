import SRWTightness.BesselDensityIntegrable

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The measure specified by the manuscript's radial transition density on positive radii. -/
noncomputable def besselDensityLaw (s x : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun y ↦ ENNReal.ofReal (besselThreeDensity s x y))

/-- The density measure is a probability measure for positive elapsed time and initial radius. -/
theorem bessel_density_law_probability (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    IsProbabilityMeasure (besselDensityLaw s x) := by
  constructor
  rw [besselDensityLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hn : ∀ᵐ y ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ besselThreeDensity s x y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (besselThreeDensity_pos s x y hs hx hy).le
  rw [← ofReal_integral_eq_lintegral_ofReal
    (bessel_density_integrable s x hs).integrableOn hn,
    bessel_density_integral_one s x hs hx, ENNReal.ofReal_one]

/-- Density integration against the literal radial transition law. -/
theorem bessel_density_law_integral (s x : ℝ) (hs : 0 < s) (hx : 0 < x) (f : ℝ → ℝ) :
    (∫ y, f y ∂besselDensityLaw s x) =
      ∫ y in Set.Ioi (0 : ℝ), besselThreeDensity s x y * f y := by
  have hm : Measurable (fun y ↦ ENNReal.ofReal (besselThreeDensity s x y)) := by
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  rw [besselDensityLaw, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (besselThreeDensity_pos s x y hs hx hy).le, smul_eq_mul]

/-- The density law is supported on positive radii. -/
theorem bessel_density_law_positive (s x : ℝ) :
    ∀ᵐ y ∂besselDensityLaw s x, 0 < y := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

end SRWTightness
