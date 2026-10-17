import SRWTightness.SourceBridgeCurvedProbability
import SRWTightness.SourceBridgeConditionalIncrement

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The complete source bridge lemma: curved survival and conditioned increments at one threshold. -/
theorem sourceBridge_lemma (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C) (hIncrement : BesselThreeIncrementInput)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H d q b : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H) →
      (q * Real.sqrt H / (2 * d) ≤
        gaussianCoefficientLaw.real (bridgeCurvedEvent (d - H) b q d γ) ∧
       gaussianCoefficientLaw.real (bridgeCurvedEvent (d - H) b q d γ) ≤
        8 * q * Real.sqrt H / d) ∧
      ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ d - H →
      Integrable (fun ω ↦
        (endpointBrownianBridge (d - H) b s ω - endpointBrownianBridge (d - H) b r ω) ^ 2)
        (ProbabilityTheory.cond gaussianCoefficientLaw (bridgeCurvedEvent (d - H) b q d γ)) ∧
      (∫ ω, (endpointBrownianBridge (d - H) b s ω -
        endpointBrownianBridge (d - H) b r ω) ^ 2
        ∂ProbabilityTheory.cond gaussianCoefficientLaw (bridgeCurvedEvent (d - H) b q d γ)) ≤
        96 * Real.exp 4 * (s - r) := by
  obtain ⟨Hp, hHp, hp⟩ := sourceBridge_curved_probability_bounds hReflection hBridge hReverse
    hPositive hInitial hHit C hMoment γ hγ hγhalf
  obtain ⟨Hi, hHi, hi⟩ := sourceBridge_conditional_increment hReflection hBridge hReverse
    hPositive hInitial hHit C hMoment hIncrement γ hγ hγhalf
  refine ⟨max Hp Hi, hHp.trans (le_max_left _ _), ?_⟩
  intro H d q b hH hd hq hb
  exact ⟨hp H d q b ((le_max_left _ _).trans hH) hd hq hb,
    hi H d q b ((le_max_right _ _).trans hH) hd hq hb⟩

end SRWTightness
