import SRWTightness.PositiveBridgeFullIncrement
import SRWTightness.ConditionalNonnegativeMoment
import SRWTightness.ConditionalSubsetLaw
import SRWTightness.SourceBridgeReversedSurvival
import SRWTightness.SourceBridgeFlatProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The source bridge conditioned directly on its curved barrier has uniformly linear increments. -/
theorem sourceBridge_conditional_increment (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C) (hIncrement : BesselThreeIncrementInput)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H d q b : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H) →
      ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ d - H →
      Integrable (fun ω ↦
        (endpointBrownianBridge (d - H) b s ω - endpointBrownianBridge (d - H) b r ω) ^ 2)
        (ProbabilityTheory.cond gaussianCoefficientLaw (bridgeCurvedEvent (d - H) b q d γ)) ∧
      (∫ ω, (endpointBrownianBridge (d - H) b s ω -
        endpointBrownianBridge (d - H) b r ω) ^ 2
        ∂ProbabilityTheory.cond gaussianCoefficientLaw (bridgeCurvedEvent (d - H) b q d γ)) ≤
        96 * Real.exp 4 * (s - r) := by
  obtain ⟨H₀, hH₀, hsurv⟩ := sourceBridge_survival_half hReflection hBridge hReverse
    hPositive hInitial hHit C hMoment γ hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro H d q b hH hd hq hb r s hr hrs hs
  have hH1 : 1 ≤ H := hH₀.trans hH
  have hd0 : 0 < d := by linarith
  have hH0 : 0 < H := by linarith
  have hq0 : 0 < q := (Real.sqrt_pos.mpr hd0).trans_le hq.1
  have ha := sourceBridge_endpoint_distance H q b hb
  have ha0 : 0 < q - b := (Real.sqrt_pos.mpr hH0).trans_le ha.1
  have hp := sourceBridge_parameter_bounds d H q (q - b) hH1 hd ha hq
  have hI := positiveBridge_full_increment hBridge hReverse hPositive hIncrement
    (d - H) q (q - b) 4 r s hp.1 hq0 ha0 hr hrs hs
    (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hp.2.2.2.1)
    (by simpa only [sub_sq_comm] using hp.2.2.2.2)
  have hhalf := hsurv H d q b hH hd hq hb
  have hrev := sourceBridge_curved_conditional_identity hReflection hReverse
    (d - H) H q b γ hp.1 hq0 (by linarith) hγ
  have hsum : H + (d - H) = d := by ring
  rw [hsum] at hrev
  rw [← hrev] at hhalf
  have hc := conditional_nonnegative_moment_half
    (positiveBridgeCoefficientLaw (d - H) q (q - b))
    (bridgeCurvedEvent (d - H) b q d γ) _ hhalf hI.1 (fun ω ↦ sq_nonneg _)
  have hbound := hc.2.trans (mul_le_mul_of_nonneg_left hI.2 (by norm_num : (0 : ℝ) ≤ 2))
  have hlaw : positiveBridgeCoefficientLaw (d - H) q (q - b) =
      ProbabilityTheory.cond gaussianCoefficientLaw (bridgeFlatEvent (d - H) b q) := by
    simp only [positiveBridgeCoefficientLaw, sub_sub_cancel]
  have hsubset : bridgeCurvedEvent (d - H) b q d γ ⊆ bridgeFlatEvent (d - H) b q := by
    intro ω hω t ht
    have hn : 0 ≤ (d - t) ^ γ := Real.rpow_nonneg (by linarith [ht.2]) _
    have hh := hω t ht
    linarith
  have hflat := sourceBridge_flat_probability_bounds hReflection d H q b hH1 hd hq hb
  have hmass : 0 < gaussianCoefficientLaw.real (bridgeFlatEvent (d - H) b q) :=
    lt_of_lt_of_le (by positivity) hflat.1
  have hn : gaussianCoefficientLaw (bridgeFlatEvent (d - H) b q) ≠ 0 := by
    intro h
    simp [Measure.real, h] at hmass
  have hlaw2 := conditional_subset_law gaussianCoefficientLaw
    (bridgeFlatEvent (d - H) b q) (bridgeCurvedEvent (d - H) b q d γ)
    (bridgeFlatEvent_nullMeasurable _ _ _) hn hsubset
  have he : (fun ω ↦ (positiveEndpointBridge (d - H) q (q - b) s ω -
      positiveEndpointBridge (d - H) q (q - b) r ω) ^ 2) =
      (fun ω ↦ (endpointBrownianBridge (d - H) b s ω -
        endpointBrownianBridge (d - H) b r ω) ^ 2) := by
    funext ω
    simp only [positiveEndpointBridge, sub_sub_cancel]
    ring
  rw [hlaw, hlaw2, he] at hc hbound
  exact ⟨hc.1, hbound.trans_eq (by ring)⟩

end SRWTightness
