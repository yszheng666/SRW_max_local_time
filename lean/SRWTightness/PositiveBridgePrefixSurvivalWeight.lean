import SRWTightness.EndpointBridgeConditionedPrefixProbability
import SRWTightness.ExternalPositiveBridge

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Every measurable positive-bridge prefix event has an explicit survival-weight formula. -/
theorem positive_bridge_prefix_survival_weight (hReflection : BridgeReflectionInput)
    (T x y r : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y)
    (hr : 0 ≤ r) (hrT : r < T) (B : Set (Set.Icc (0 : ℝ) r → ℝ)) (hB : MeasurableSet B) :
    (positiveBridgeCoefficientLaw T x y).real {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ positiveEndpointBridge T x y t ω) ∈ B} =
    (∫ ω in {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ positiveEndpointBridge T x y t ω) ∈ B ∧
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T (x - y) t ω) ∈
        dyadicFlatPathEvent r x ∧ 0 < positiveEndpointBridge T x y r ω},
      1 - Real.exp (-(2 * positiveEndpointBridge T x y r ω * y / (T - r)))
        ∂gaussianCoefficientLaw) / (1 - Real.exp (-(2 * x * y / T))) := by
  let H : (Set.Icc (0 : ℝ) r → ℝ) → (Set.Icc (0 : ℝ) r → ℝ) :=
    fun p t ↦ x - p t
  have hH : Measurable H := by dsimp [H]; fun_prop
  have he := endpoint_bridge_conditioned_prefix_probability hReflection T (x - y) x r
    hT hx (by linarith) hr hrT (H ⁻¹' B) (hB.preimage hH)
  have hxy : x - (x - y) = y := by ring
  simpa only [positiveBridgeCoefficientLaw, positiveEndpointBridge, H, Set.mem_preimage,
    sub_pos, hxy] using he

end SRWTightness
