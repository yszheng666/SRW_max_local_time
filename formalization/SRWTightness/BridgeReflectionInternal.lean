import SRWTightness.AntitoneIntegralIdentification
import SRWTightness.BridgeReflectionCandidate
import SRWTightness.BridgeFlatProbabilityMonotone

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The original bridge reflection input follows from the actual Gaussian path construction. -/
theorem bridge_reflection_input_internal : BridgeReflectionInput := by
  intro T b q hT hq hb
  apply antitone_eq_of_prefix_integrals (gaussianReal 0 T.toNNReal)
    (fun a c hac ↦ gaussian_endpoint_interval_pos T a c hT hac)
    (fun a ↦ gaussianCoefficientLaw.real (bridgeFlatEvent T a q))
    (fun a ↦ 1 - Real.exp (-(2 * q * (q - a) / T))) q
    (bridge_flat_probability_antitone T q hT)
  · intro x hx
    fun_prop
  · intro c hc
    exact (bridge_flat_probability_integrable T q hT (gaussianReal 0 T.toNNReal)).integrableOn
  · intro c hc
    exact bridge_reflection_candidate_integrable T q c hT hq hc
  · intro c hc
    exact bridge_reflection_integrated T q c hT hq hc
  · exact hb

end SRWTightness
