import SRWTightness.BesselDensityLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Integrability under the Bessel law is precisely integrability against its literal density. -/
theorem bessel_density_integrable_iff (s x : ℝ) (hs : 0 < s) (hx : 0 < x)
    (f : ℝ → ℝ) :
    Integrable f (besselDensityLaw s x) ↔
      IntegrableOn (fun z ↦ besselThreeDensity s x z * f z) (Set.Ioi (0 : ℝ)) := by
  have hm : Measurable (fun z ↦ ENNReal.ofReal (besselThreeDensity s x z)) := by
    unfold besselThreeDensity killedBrownianDensity
    fun_prop
  rw [besselDensityLaw, integrable_withDensity_iff_integrable_smul' hm
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [ENNReal.toReal_ofReal (besselThreeDensity_pos s x z hs hx hz).le, smul_eq_mul]

end SRWTightness
