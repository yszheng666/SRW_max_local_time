import SRWTightness.EndpointBridgeConditionedPrefixProbability
import SRWTightness.BridgePrefixHeatKernelIntegral
import SRWTightness.BridgeSurvivalKilledKernelRatio

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The conditioned bridge prefix is represented by surviving Brownian paths and killed kernels. -/
theorem endpoint_bridge_conditioned_killed_prefix (hReflection : BridgeReflectionInput)
    (T b q r : ℝ) (hT : 0 < T) (hq : 0 < q) (hbq : b < q)
    (hr : 0 < r) (hrT : r < T) (B : Set (Set.Icc (0 : ℝ) r → ℝ)) (hB : MeasurableSet B) :
    (cond gaussianCoefficientLaw (bridgeFlatEvent T b q)).real {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b t ω) ∈ B} =
    ∫ ω in {ω |
      (fun t : Set.Icc (0 : ℝ) r ↦ Real.sqrt r * gaussianDyadicPath ω (t / r)) ∈ B ∧
      (fun t : Set.Icc (0 : ℝ) r ↦ Real.sqrt r * gaussianDyadicPath ω (t / r)) ∈
        dyadicFlatPathEvent r q ∧ Real.sqrt r * gaussianDyadicPath ω (r / r) < q},
      killedBrownianDensity (T - r) (q - Real.sqrt r * gaussianDyadicPath ω (r / r)) (q - b) /
        killedBrownianDensity T q (q - b) ∂gaussianCoefficientLaw := by
  let e : Set.Icc (0 : ℝ) r := ⟨r, hr.le, le_rfl⟩
  let A : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | p ∈ B ∧ p ∈ dyadicFlatPathEvent r q ∧ p e < q}
  let c := 1 - Real.exp (-(2 * q * (q - b) / T))
  let f := fun p : Set.Icc (0 : ℝ) r → ℝ ↦
    (1 - Real.exp (-(2 * (q - p e) * (q - b) / (T - r)))) / c
  let P := fun ω (t : Set.Icc (0 : ℝ) r) ↦ endpointBrownianBridge T b t ω
  let W := fun ω (t : Set.Icc (0 : ℝ) r) ↦
    Real.sqrt r * gaussianDyadicPath ω (t / r)
  have hA : MeasurableSet A := hB.inter ((dyadicFlatPathEvent_measurable r q).inter
    (measurableSet_lt (measurable_pi_apply e) measurable_const))
  have hf : Measurable f := by dsimp [f]; fun_prop
  rw [endpoint_bridge_conditioned_prefix_probability hReflection T b q r hT hq hbq
    hr.le hrT B hB, ← integral_div]
  change (∫ ω in {ω |
      (fun u : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b u ω) ∈ A},
      f (fun u : Set.Icc (0 : ℝ) r ↦ endpointBrownianBridge T b u ω)
        ∂gaussianCoefficientLaw) = _
  rw [bridge_prefix_heat_kernel_integral T b r hT hr hrT A hA f hf]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω ↦ bridge_survival_killed_kernel_ratio T r q b
    (Real.sqrt r * gaussianDyadicPath ω (r / r)) hT hrT)

end SRWTightness
