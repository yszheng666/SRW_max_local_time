import SRWTightness.PositiveBridgeFailureThreshold
import SRWTightness.PositiveBridgeSurvival
import SRWTightness.SourceBridgeParameters

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Source endpoint windows and explicit large scales give curved survival at least one half. -/
theorem sourceBridge_survival_half (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H d q b : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H) →
      1 / 2 ≤ (positiveBridgeCoefficientLaw (d - H) (q - b) q).real
        {ω | ∀ t ∈ Set.Icc (0 : ℝ) (d - H),
          (H + t) ^ γ ≤ positiveEndpointBridge (d - H) (q - b) q t ω} := by
  obtain ⟨H₀, hH₀, hsmall⟩ := positiveBridge_failure_half hBridge hReverse hPositive
    hInitial hHit C hMoment γ 4 hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro H d q b hH hd hq hb
  have hH1 : 1 ≤ H := hH₀.trans hH
  have hp := sourceBridge_parameter_bounds d H q (q - b) hH1 hd
    (sourceBridge_endpoint_distance H q b hb) hq
  have hfail := hsmall H (d - H) (q - b) q hH hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  have ha : 0 < q - b := (Real.sqrt_pos.mpr (by linarith : 0 < H)).trans_le hp.2.1
  have hq0 : 0 < q := (Real.sqrt_pos.mpr (by linarith : 0 < d)).trans_le hq.1
  rw [positiveBridge_survival_real hReflection (d - H) (q - b) q (d - H) hp.1 ha hq0
    (fun t ↦ (H + t) ^ γ)
    ((Real.continuous_rpow_const hγ).comp (continuous_const.add continuous_id))]
  linarith

end SRWTightness
