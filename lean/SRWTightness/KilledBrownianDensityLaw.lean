import SRWTightness.BesselDensityLaplace
import SRWTightness.KilledGaussianReflectionIntegral
import SRWTightness.GaussianReflectionMass

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The literal killed Brownian density is Lebesgue integrable. -/
theorem killed_brownian_density_integrable (s x : ℝ) (hs : 0 < s) :
    Integrable (killedBrownianDensity s x) := by
  have hi := integrable_gaussianPDFReal x s.toNNReal
  apply (hi.sub hi.comp_neg).congr
  exact ae_of_all _ (fun y ↦ (killed_brownian_density_gaussian s x y hs).symm)

/-- The subprobability measure specified by the source killed Brownian density. -/
noncomputable def killedBrownianDensityLaw (s x : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun y ↦ ENNReal.ofReal (killedBrownianDensity s x y))

/-- The killed density measure is finite for positive time and initial position. -/
theorem killed_brownian_density_law_finite (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    IsFiniteMeasure (killedBrownianDensityLaw s x) := by
  constructor
  rw [killedBrownianDensityLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hn : ∀ᵐ y ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ killedBrownianDensity s x y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (killedBrownianDensity_pos s x y hs hx hy).le
  rw [← ofReal_integral_eq_lintegral_ofReal
    (killed_brownian_density_integrable s x hs).integrableOn hn]
  exact ENNReal.ofReal_lt_top

/-- Integration against the literal killed Brownian density measure. -/
theorem killed_brownian_density_law_integral (s x : ℝ) (hs : 0 < s) (hx : 0 < x)
    (f : ℝ → ℝ) :
    (∫ y, f y ∂killedBrownianDensityLaw s x) =
      ∫ y in Set.Ioi (0 : ℝ), killedBrownianDensity s x y * f y := by
  have hm : Measurable (fun y ↦ ENNReal.ofReal (killedBrownianDensity s x y)) := by
    unfold killedBrownianDensity
    fun_prop
  rw [killedBrownianDensityLaw, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (killedBrownianDensity_pos s x y hs hx hy).le, smul_eq_mul]

/-- The killed kernel's total mass is exactly the central Gaussian probability. -/
theorem killed_brownian_density_integral (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    (∫ y in Set.Ioi (0 : ℝ), killedBrownianDensity s x y) =
      (gaussianReal 0 s.toNNReal).real (Set.Icc (-x) x) := by
  have he := killed_gaussian_reflection_integral s x hs (fun _ ↦ 1)
  simp only [mul_one] at he
  rw [← he]
  exact gaussian_reflection_mass s x hs hx.le

end SRWTightness
