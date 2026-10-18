import SRWTightness.ScaledGaussianPathLaw
import SRWTightness.EndpointKilledProductLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Under nonnegative survival, the actual Brownian endpoint has the literal killed density. -/
theorem scaled_gaussian_killed_probability (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) (A : Set ℝ) (hA : MeasurableSet A) :
    gaussianCoefficientLaw.real {ω |
      x - Real.sqrt T * gaussianDyadicPath ω (T / T) ∈ A ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ x} =
      (killedBrownianDensityLaw T x).real A := by
  let C : Set (ℝ × (Set.Icc (0 : ℝ) T → ℝ)) :=
    {p | x - p.1 ∈ A ∧ p.2 ∈ dyadicFlatPathEvent T x}
  have hC : MeasurableSet C :=
    (hA.preimage (measurable_const.sub measurable_fst)).inter
      ((dyadicFlatPathEvent_measurable T x).preimage measurable_snd)
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
  have he := congrArg (fun ν : Measure (ℝ × (Set.Icc (0 : ℝ) T → ℝ)) ↦ ν.real C)
    (scaled_gaussian_endpoint_bridge_law T hT)
  rw [map_measureReal_apply hm hC, map_measureReal_apply hn hC] at he
  have hleft : gaussianCoefficientLaw.real {ω |
      x - Real.sqrt T * gaussianDyadicPath ω (T / T) ∈ A ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ x} =
      gaussianCoefficientLaw.real ((fun ω ↦
        (Real.sqrt T * gaussianDyadicPath ω (T / T),
          fun t : Set.Icc (0 : ℝ) T ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))) ⁻¹' C) := by
    apply measureReal_congr
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    apply propext
    apply and_congr_right
    intro hAω
    exact continuous_flat_iff_dyadic _
      (continuous_const.mul (hω.comp (continuous_id.div_const T))) T x
  exact hleft.trans (he.trans (endpoint_killed_product_law hReflection T x hT hx A hA))

end SRWTightness
