import SRWTightness.ScaledGaussianPathLaw
import SRWTightness.EndpointFlatReflectionProbability

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual scaled Brownian path and independent endpoint/bridge have equal path laws. -/
theorem scaled_gaussian_bridge_path_law (T : ℝ) (hT : 0 < T) :
    gaussianCoefficientLaw.map (fun ω (t : Set.Icc (0 : ℝ) T) ↦
      Real.sqrt T * gaussianDyadicPath ω (t / T)) =
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).map
        (fun p (t : Set.Icc (0 : ℝ) T) ↦ endpointBrownianBridge T p.1 t p.2) := by
  have hm : Measurable (fun ω ↦
      (Real.sqrt T * gaussianDyadicPath ω (T / T),
        fun t : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))) := by
    apply Measurable.prodMk
    · exact measurable_const.mul (gaussianDyadicPath_measurable _)
    · exact measurable_pi_lambda _ (fun t ↦
        measurable_const.mul (gaussianDyadicPath_measurable _))
  have hn : Measurable (fun p : ℝ × GaussianCoefficientSpace ↦
      (p.1, fun t : Set.Icc (0 : ℝ) T ↦ endpointBrownianBridge T p.1 t p.2)) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro t
    exact ((actualIntervalBridge_measurable T t).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  have he := congrArg (fun ν : Measure (ℝ × (Set.Icc (0 : ℝ) T → ℝ)) ↦
    ν.map Prod.snd) (scaled_gaussian_endpoint_bridge_law T hT)
  rw [Measure.map_map measurable_snd hm, Measure.map_map measurable_snd hn] at he
  exact he

/-- Reflection gives the full actual Brownian flat-barrier probability. -/
theorem scaled_gaussian_flat_probability (hReflection : BridgeReflectionInput)
    (T q : ℝ) (hT : 0 < T) (hq : 0 < q) :
    gaussianCoefficientLaw.real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
        Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ q} =
      (gaussianReal 0 T.toNNReal).real (Set.Icc (-q) q) := by
  have hm : Measurable (fun ω (t : Set.Icc (0 : ℝ) T) ↦
      Real.sqrt T * gaussianDyadicPath ω (t / T)) :=
    measurable_pi_lambda _ (fun t ↦
      measurable_const.mul (gaussianDyadicPath_measurable _))
  have hn : Measurable (fun p : ℝ × GaussianCoefficientSpace ↦
      fun t : Set.Icc (0 : ℝ) T ↦ endpointBrownianBridge T p.1 t p.2) := by
    apply measurable_pi_lambda
    intro t
    exact ((actualIntervalBridge_measurable T t).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  have he := congrArg (fun ν : Measure (Set.Icc (0 : ℝ) T → ℝ) ↦
    ν.real (dyadicFlatPathEvent T q)) (scaled_gaussian_bridge_path_law T hT)
  rw [map_measureReal_apply hm (dyadicFlatPathEvent_measurable T q),
    map_measureReal_apply hn (dyadicFlatPathEvent_measurable T q)] at he
  have hleft : gaussianCoefficientLaw.real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T,
        Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ q} =
      gaussianCoefficientLaw.real ((fun ω (t : Set.Icc (0 : ℝ) T) ↦
        Real.sqrt T * gaussianDyadicPath ω (t / T)) ⁻¹' dyadicFlatPathEvent T q) := by
    apply measureReal_congr
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    exact propext (continuous_flat_iff_dyadic _
      (continuous_const.mul (hω.comp (continuous_id.div_const T))) T q)
  exact hleft.trans (he.trans (endpoint_flat_reflection_probability hReflection T q hT hq))

end SRWTightness
