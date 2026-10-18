import SRWTightness.SourceBridgeLemma
import SRWTightness.EndpointBridgeSectionLaw
import SRWTightness.ConditionalMomentIntegral

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The source bridge increment bound as a restricted integral on the measurable endpoint section. -/
theorem sourceBridge_section_moment (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C) (hIncrement : BesselThreeIncrementInput)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H d q b : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H) →
      ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ d - H →
      let E := Prod.mk b ⁻¹' endpointBridgeProductEvent (d - H)
        (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ
      let f := fun ω ↦ (endpointBrownianBridge (d - H) b s ω -
        endpointBrownianBridge (d - H) b r ω) ^ 2
      Integrable f (gaussianCoefficientLaw.restrict E) ∧
        (∫ ω in E, f ω ∂gaussianCoefficientLaw) ≤
          (96 * Real.exp 4 * (s - r)) * gaussianCoefficientLaw.real E := by
  obtain ⟨H₀, hH₀, hp⟩ := sourceBridge_lemma hReflection hBridge hReverse hPositive
    hInitial hHit C hMoment hIncrement γ hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro H d q b hH hd hq hb r s hr hrs hs
  dsimp only
  have hh := hp H d q b hH hd hq hb
  have hH0 : 0 < H := by linarith
  have hd0 : 0 < d := by linarith
  have hq0 : 0 < q := (Real.sqrt_pos.mpr hd0).trans_le hq.1
  have hpos : 0 < gaussianCoefficientLaw.real (bridgeCurvedEvent (d - H) b q d γ) :=
    lt_of_lt_of_le (by positivity) hh.1.1
  have hi := hh.2 r s hr hrs hs
  have he := endpointBridgeProductEvent_section_cond (d - H)
    (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ b hγ hb
  have hm := endpointBridgeProductEvent_section (d - H)
    (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ b hγ hb
  rw [← he] at hi
  exact conditional_moment_event_integral _ _ _ (by rwa [hm]) hi.1 _ hi.2

end SRWTightness
