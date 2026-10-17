import SRWTightness.EndpointBridgeProductEvent
import SRWTightness.ProductEventRealBounds
import SRWTightness.SourceGaussianEndpointWindow

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Endpoint-window and curved-bridge costs combine to order sqrt(H)/d, uniformly in the source band. -/
theorem source_endpoint_bridge_probability (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ c C : ℝ, 1 ≤ H₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ H d q : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      c * Real.sqrt H / d ≤
        ((gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw).real
          (endpointBridgeProductEvent (d - H) (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ) ∧
      ((gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw).real
          (endpointBridgeProductEvent (d - H) (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ) ≤
        C * Real.sqrt H / d := by
  obtain ⟨H₀, hH₀, hb⟩ := sourceBridge_curved_probability_bounds hReflection hBridge hReverse
    hPositive hInitial hHit Cm hMoment γ hγ hγhalf
  obtain ⟨c, C, hc, hC, he⟩ := source_endpoint_window_probability hGaussian
  refine ⟨H₀, c / 2, 16 * C, hH₀, by positivity, by positivity, ?_⟩
  intro H d q hH hd hq
  have hH1 : 1 ≤ H := hH₀.trans hH
  have hd0 : 0 < d := by linarith
  have hrd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hq0 : 0 ≤ q := hrd.le.trans hq.1
  have hep := he d H q hH1 hd hq
  have hprod := product_event_real_bounds
    (gaussianReal 0 (d - H).toNNReal) gaussianCoefficientLaw
    (Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H))
    (endpointBridgeProductEvent (d - H) (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ)
    (q * Real.sqrt H / (2 * d)) (8 * q * Real.sqrt H / d)
    (by positivity) (by positivity) measurableSet_Icc
    (endpointBridgeProductEvent_measurable _ _ _ _ _ _)
    (endpointBridgeProductEvent_subset _ _ _ _ _ _) (by
      intro b hbwin
      rw [endpointBridgeProductEvent_section _ _ _ _ _ _ _ hγ hbwin]
      exact hb H d q b hH hd hq hbwin)
  constructor
  · apply le_trans _ hprod.1
    calc
      _ = (Real.sqrt d * Real.sqrt H / (2 * d)) * (c / Real.sqrt d) := by
        field_simp
        <;> ring
      _ ≤ (q * Real.sqrt H / (2 * d)) * (c / Real.sqrt d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hq.1 (Real.sqrt_nonneg H)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hep.1 (by positivity)
  · apply hprod.2.trans
    calc
      _ ≤ (8 * q * Real.sqrt H / d) * (C / Real.sqrt d) :=
        mul_le_mul_of_nonneg_left hep.2 (by positivity)
      _ ≤ (8 * (2 * Real.sqrt d) * Real.sqrt H / d) * (C / Real.sqrt d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ hd0.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq.2 (by norm_num)) (Real.sqrt_nonneg H)
      _ = _ := by
        field_simp
        <;> ring

end SRWTightness
