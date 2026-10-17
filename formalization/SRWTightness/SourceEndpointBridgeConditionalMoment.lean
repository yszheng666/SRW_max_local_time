import SRWTightness.SourceEndpointBridgeMoment
import SRWTightness.SourceEndpointBridgeProbability
import SRWTightness.ConditionalMomentProduct

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The full endpoint-window and curve conditioning has a uniform increment second moment. -/
theorem sourceEndpointBridge_conditional_moment (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C) (hIncrement : BesselThreeIncrementInput)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H d q : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ d - H →
      let μ := (gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw
      let E := endpointBridgeProductEvent (d - H)
        (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ
      let f := fun p : ℝ × GaussianCoefficientSpace ↦
        (endpointBrownianBridge (d - H) p.1 s p.2 -
          endpointBrownianBridge (d - H) p.1 r p.2) ^ 2
      Integrable f (ProbabilityTheory.cond μ E) ∧
        (∫ p, f p ∂ProbabilityTheory.cond μ E) ≤ 96 * Real.exp 4 * (s - r) := by
  obtain ⟨Hi, hHi, hi⟩ := sourceEndpointBridge_moment hReflection hBridge hReverse
    hPositive hInitial hHit C hMoment hIncrement γ hγ hγhalf
  obtain ⟨Hp, c, Cp, hHp, hc, hCp, hp⟩ := source_endpoint_bridge_probability hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit C γ hMoment hγ hγhalf
  refine ⟨max Hi Hp, hHi.trans (le_max_left _ _), ?_⟩
  intro H d q hH hd hq r s hr hrs hs
  dsimp only
  have hHiH := (le_max_left Hi Hp).trans hH
  have hHpH := (le_max_right Hi Hp).trans hH
  have hH0 : 0 < H := by linarith
  have hd0 : 0 < d := by linarith
  have hh := hi H d q hHiH hd hq r s hr hrs hs
  have hb := hp H d q hHpH hd hq
  exact event_integral_conditional_moment _ _ _
    (lt_of_lt_of_le (by positivity) hb.1) hh.1 _ hh.2

end SRWTightness
