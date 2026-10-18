import SRWTightness.ScaledGaussianPathLaw
import SRWTightness.DyadicFlatPathEvent
import SRWTightness.FlatBridgeProductIntegral

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Brownian barrier and endpoint probability disintegrates over actual bridge laws. -/
theorem scaled_gaussian_flat_disintegration (T q b : ℝ) (hT : 0 < T) :
    gaussianCoefficientLaw.real {ω |
      (∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ q) ∧
      Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b} =
    ∫ a in Set.Iic b, gaussianCoefficientLaw.real (bridgeFlatEvent T a q)
      ∂gaussianReal 0 T.toNNReal := by
  let P : GaussianCoefficientSpace → ℝ × (Set.Icc (0 : ℝ) T → ℝ) := fun ω ↦
    (Real.sqrt T * gaussianDyadicPath ω (T / T),
      fun t ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))
  let Q : ℝ × GaussianCoefficientSpace → ℝ × (Set.Icc (0 : ℝ) T → ℝ) := fun p ↦
    (p.1, fun t ↦ endpointBrownianBridge T p.1 t p.2)
  let A := Set.Iic b ×ˢ dyadicFlatPathEvent T q
  let E := Q ⁻¹' A
  have hP : Measurable P := (measurable_const.mul (gaussianDyadicPath_measurable _)).prodMk
    (measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _)))
  have hQ : Measurable Q := measurable_fst.prodMk (measurable_pi_lambda _ (fun t ↦
    ((actualIntervalBridge_measurable T t).comp measurable_snd).add
      (measurable_const.mul measurable_fst)))
  have hA : MeasurableSet A := measurableSet_Iic.prod (dyadicFlatPathEvent_measurable T q)
  have hE : MeasurableSet E := hA.preimage hQ
  have he := congrArg (fun μ : Measure (ℝ × (Set.Icc (0 : ℝ) T → ℝ)) ↦ μ.real A)
    (scaled_gaussian_endpoint_bridge_law T hT)
  rw [map_measureReal_apply hP hA, map_measureReal_apply hQ hA] at he
  have hleft : gaussianCoefficientLaw.real {ω |
      (∀ t ∈ Set.Icc (0 : ℝ) T, Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ q) ∧
      Real.sqrt T * gaussianDyadicPath ω (T / T) ≤ b} =
      gaussianCoefficientLaw.real (P ⁻¹' A) := by
    apply measureReal_congr
    filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
    apply propext
    have hc := continuous_flat_iff_dyadic
      (fun t ↦ Real.sqrt T * gaussianDyadicPath ω (t / T))
      (continuous_const.mul (hω.comp (continuous_id.div_const T))) T q
    change (_ ∧ _) ↔ (_ ∧ _)
    tauto
  rw [hleft, he, product_event_real_integral _ _ E hE]
  have hsection (a : ℝ) : gaussianCoefficientLaw.real (Prod.mk a ⁻¹' E) =
      (Set.Iic b).indicator (fun a ↦ gaussianCoefficientLaw.real (bridgeFlatEvent T a q)) a := by
    by_cases ha : a ≤ b
    · rw [Set.indicator_of_mem (show a ∈ Set.Iic b from ha)]
      have hs : Prod.mk a ⁻¹' E = Prod.mk a ⁻¹' endpointFlatProductEvent T q := by
        ext ω
        change (a ≤ b ∧ _) ↔ _
        exact and_iff_right ha
      rw [hs, endpointFlatProductEvent_section]
    · rw [Set.indicator_of_notMem (show a ∉ Set.Iic b from ha)]
      have hs : Prod.mk a ⁻¹' E = ∅ := by
        ext ω
        change (a ≤ b ∧ _) ↔ False
        tauto
      rw [hs, measureReal_empty]
  simp_rw [hsection]
  rw [integral_indicator measurableSet_Iic]

end SRWTightness
