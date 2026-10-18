import SRWTightness.ActualBesselTransitionDensity
import SRWTightness.ActualKilledBrownianDensity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The literal Bessel measure is the linear Doob transform of the killed Brownian measure. -/
theorem bessel_killed_density_transform (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    besselDensityLaw s x = (killedBrownianDensityLaw s x).withDensity
      (fun y ↦ ENNReal.ofReal (y / x)) := by
  have hf : Measurable (fun y ↦ ENNReal.ofReal (killedBrownianDensity s x y)) := by
    unfold killedBrownianDensity
    fun_prop
  have hg : Measurable (fun y : ℝ ↦ ENNReal.ofReal (y / x)) := by fun_prop
  rw [besselDensityLaw, killedBrownianDensityLaw, ← withDensity_mul _ hf hg]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change ENNReal.ofReal ((y / x) * killedBrownianDensity s x y) = _
  rw [ENNReal.ofReal_mul (div_nonneg hy.le hx.le), mul_comm]
  rfl

/-- Actual Bessel endpoints are the Doob transform of actual killed Brownian endpoints. -/
theorem actual_bessel_killed_endpoint_transform (hReflection : BridgeReflectionInput)
    (T x s : ℝ) (hT : 0 < T) (hx : 0 < x) (hs : 0 < s) (hsT : s ≤ T) :
    (independentBridgeLaw (Fin 3)).map (actualBesselThree T x s) =
      ((gaussianCoefficientLaw.restrict
        {ω | ∀ t ∈ Set.Icc (0 : ℝ) s,
          0 < x - Real.sqrt s * gaussianDyadicPath ω (t / s)}).map
        (fun ω ↦ x - Real.sqrt s * gaussianDyadicPath ω (s / s))).withDensity
          (fun y ↦ ENNReal.ofReal (y / x)) := by
  rw [(actual_bessel_transition_density T x s hT hx hs hsT).map_eq,
    actual_killed_brownian_transition_density hReflection s x hs hx]
  exact bessel_killed_density_transform s x hs hx

end SRWTightness
