import SRWTightness.EndpointBridgeProductEvent
import SRWTightness.GaussianMiddleKernelBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Exact real-valued Fubini formula for measurable product events with finite sections. -/
theorem product_event_real_integral {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [IsFiniteMeasure ν]
    (E : Set (Ω × Ξ)) (hE : MeasurableSet E) :
    (μ.prod ν).real E = ∫ x, ν.real (Prod.mk x ⁻¹' E) ∂μ := by
  rw [Measure.real, Measure.prod_apply hE]
  exact (integral_toReal (measurable_measure_prodMk_left hE).aemeasurable
    (ae_of_all _ fun x ↦ measure_lt_top ν _)).symm

/-- Reflection integrates over the endpoint interval; its upper boundary has Gaussian mass zero. -/
theorem flat_bridge_product_integral (hReflection : BridgeReflectionInput)
    (T q a b : ℝ) (hT : 0 < T) (hq : 0 < q) (hab : a ≤ b) (hbq : b ≤ q) :
    ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).real
      (endpointBridgeProductEvent T a b (q + 1) 0 0) =
      ∫ s in Set.Icc a b, gaussianPDFReal 0 T.toNNReal s *
        (1 - Real.exp (-(2 * q * (q - s) / T))) := by
  let μ := gaussianReal 0 T.toNNReal
  let E := endpointBridgeProductEvent T a b (q + 1) 0 0
  let f := fun x ↦ gaussianCoefficientLaw.real (Prod.mk x ⁻¹' E)
  have hout (x : ℝ) (hx : x ∉ Set.Icc a b) : f x = 0 := by
    have he : Prod.mk x ⁻¹' E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hx hω.1
    simp only [f, he, measureReal_empty]
  rw [product_event_real_integral _ _ E (endpointBridgeProductEvent_measurable _ _ _ _ _ _)]
  have hind : f = (Set.Icc a b).indicator f := by
    funext x
    by_cases hx : x ∈ Set.Icc a b
    · exact (Set.indicator_of_mem hx f).symm
    · rw [hout x hx, Set.indicator_of_notMem hx]
  change (∫ x, f x ∂μ) = _
  conv_lhs => rw [hind, integral_indicator measurableSet_Icc]
  rw [← gaussian_real_set_integral_density _ _ measurableSet_Icc T hT]
  apply integral_congr_ae
  letI : NullSingletonClass μ :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hT))
  have hne : ∀ᵐ x ∂μ, x ≠ q := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with x hx hnx
  have hsection := endpointBridgeProductEvent_section T a b (q + 1) 0 0 x le_rfl hx
  have he : bridgeCurvedEvent T x (q + 1) 0 0 = bridgeFlatEvent T x q := by
    ext ω
    simp only [bridgeCurvedEvent, bridgeFlatEvent, Set.mem_setOf_eq,
      Real.rpow_zero, add_sub_cancel_right]
  rw [he] at hsection
  exact hsection.trans (hReflection T x q hT hq (lt_of_le_of_ne (hx.2.trans hbq) hnx))

end SRWTightness
