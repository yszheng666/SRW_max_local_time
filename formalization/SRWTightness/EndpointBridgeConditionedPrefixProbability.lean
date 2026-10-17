import SRWTightness.EndpointBridgeFlatPrefixProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The flat-survival-conditioned prefix has the exact normalized future survival weight. -/
theorem endpoint_bridge_conditioned_prefix_probability (hReflection : BridgeReflectionInput)
    (T b q r : ℝ) (hT : 0 < T) (hq : 0 < q) (hbq : b < q)
    (hr : 0 ≤ r) (hrT : r < T) (B : Set (Set.Icc (0 : ℝ) r → ℝ)) (hB : MeasurableSet B) :
    (cond gaussianCoefficientLaw (bridgeFlatEvent T b q)).real {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ B} =
    (∫ ω in {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ B ∧
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ dyadicFlatPathEvent r q ∧
      endpointBrownianBridge T b r ω < q},
      1 - Real.exp (-(2 * (q - endpointBrownianBridge T b r ω) * (q - b) / (T - r)))
        ∂gaussianCoefficientLaw) / (1 - Real.exp (-(2 * q * (q - b) / T))) := by
  have hm : Measurable (fun ω (t : Set.Icc (0 : ℝ) r) ↦
      endpointBrownianBridge T b t ω) :=
    measurable_pi_lambda _ (fun t ↦
      (actualIntervalBridge_measurable T t).add measurable_const)
  have he := endpoint_bridge_flat_prefix_probability hReflection T b q r hT hq hbq
    hr hrT B hB
  have hE : MeasurableSet {ω : GaussianCoefficientSpace |
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ B} := hB.preimage hm
  have hcond := cond_apply' (s := bridgeFlatEvent T b q) hE gaussianCoefficientLaw
  unfold Measure.real
  rw [hcond,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (gaussianCoefficientLaw.real (bridgeFlatEvent T b q))⁻¹ *
    gaussianCoefficientLaw.real {ω | ω ∈ bridgeFlatEvent T b q ∧
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ B} = _
  rw [he, hReflection T b q hT hq hbq]
  ring

end SRWTightness
