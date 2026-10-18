import SRWTightness.BesselBridgeDoobPrefixLaw
import SRWTightness.PositiveBridgeDoobPrefixProbability
import SRWTightness.BesselBridgeWeightNormalization
import SRWTightness.PositiveBridgeSurvival
import SRWTightness.PositiveBridgeCrossingEvent

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The exact original positive-bridge restriction identity follows from reflection alone. -/
theorem positive_bridge_restriction_input_internal (hReflection : BridgeReflectionInput) :
    PositiveBridgeRestrictionInput := by
  intro T x y s hT hx hy hs hsT
  letI := positiveBridge_probability hReflection T x y hT hx hy
  letI := bessel_bridge_weight_probability T x y s hT hx hy hs hsT
  have hD : Measurable (fun ω (u : Set.Icc (0 : ℝ) s) ↦
      x - Real.sqrt s * gaussianDyadicPath ω (u / s)) :=
    measurable_pi_lambda _ (fun _ ↦
      measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _)))
  apply Measure.ext
  intro B hB
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((positiveBridgeCoefficientLaw T x y).map
      (fun ω (u : Set.Icc (0 : ℝ) s) ↦ positiveEndpointBridge T x y u ω)).real B =
    (((independentBridgeLaw (Fin 3)).withDensity
      (fun ω ↦ ENNReal.ofReal (besselThreeDensity (T - s) (actualBesselThree T x s ω) y /
        besselThreeDensity T x y))).map
      (fun ω (u : Set.Icc (0 : ℝ) s) ↦ actualBesselThree T x u ω)).real B
  rw [map_measureReal_apply (positiveEndpointBridge_path_measurable T x y s) hB,
    bessel_bridge_doob_prefix_law hReflection T x y s hT hx hs hsT,
    map_measureReal_apply hD hB]
  exact positive_bridge_doob_prefix_probability hReflection T x y s hT hx hy hs hsT B hB

end SRWTightness
