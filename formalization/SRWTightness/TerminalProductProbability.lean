import SRWTightness.TerminalBridgeProductEvent
import SRWTightness.SourceEndpointBridgeProbability
import SRWTightness.GaussianWindowInputReduction

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- For fixed source cutoff and bounded site errors, all three Gaussian constraints cost order 1/d. -/
theorem terminal_product_probability (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H ε K D : ℝ, H₀ ≤ H → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d q At V Δ : ℝ,
      256 * H ≤ d → q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      let μ := ((gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw).prod
        (gaussianReal 0 Δ.toNNReal)
      let E := terminalBridgeProductEvent (d - H) (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      c / d ≤ μ.real E ∧ μ.real E ≤ C / d := by
  obtain ⟨H₀, cb, Cb, hH₀, hcb, hCb, hb⟩ := source_endpoint_bridge_probability hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro H ε K D hH hε hK hD
  obtain ⟨cw, hcw, hw⟩ := terminalBridge_product_probability
    (gaussianIntervalInput_unitWindow hGaussian) (Real.sqrt H) ε K D hε hK hD
  have hroot : 0 < Real.sqrt H := Real.sqrt_pos.mpr (by linarith)
  refine ⟨cw * cb * Real.sqrt H, Cb * Real.sqrt H, by positivity, by positivity, ?_⟩
  intro d q At V Δ hd hq hAt hV hΔ
  dsimp only
  have hb' := hb H d q hH hd hq
  have hw' := hw (d - H) At V d q Δ γ hAt hV hΔ
  constructor
  · calc
      _ = cw * (cb * Real.sqrt H / d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb'.1 hcw.le
      _ ≤ _ := hw'.1
  · exact hw'.2.trans hb'.2

end SRWTightness
