import SRWTightness.SourceBridgeReversedSurvival
import SRWTightness.BridgeConditionalProbability
import SRWTightness.SourceBridgeFlatProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Source (7.12) with explicit constants, conditional on the listed standard bridge inputs. -/
theorem sourceBridge_curved_probability_bounds (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H d q b : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H) →
      q * Real.sqrt H / (2 * d) ≤
        gaussianCoefficientLaw.real (bridgeCurvedEvent (d - H) b q d γ) ∧
      gaussianCoefficientLaw.real (bridgeCurvedEvent (d - H) b q d γ) ≤
        8 * q * Real.sqrt H / d := by
  obtain ⟨H₀, hH₀, hsurv⟩ := sourceBridge_survival_half hReflection hBridge hReverse
    hPositive hInitial hHit C hMoment γ hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro H d q b hH hd hq hb
  have hH1 : 1 ≤ H := hH₀.trans hH
  have hd0 : 0 < d := by linarith
  have hH0 : 0 < H := by linarith
  have hq0 : 0 < q := (Real.sqrt_pos.mpr hd0).trans_le hq.1
  have hbq : b < q := by linarith [hb.2, Real.sqrt_pos.mpr hH0]
  have hT : 0 < d - H := by linarith
  have hflat := sourceBridge_flat_probability_bounds hReflection d H q b hH1 hd hq hb
  have hmass : 0 < gaussianCoefficientLaw.real (bridgeFlatEvent (d - H) b q) :=
    lt_of_lt_of_le (by positivity) hflat.1
  have hsubset : bridgeCurvedEvent (d - H) b q d γ ⊆
      bridgeFlatEvent (d - H) b q := by
    intro ω hω t ht
    have hn : 0 ≤ (d - t) ^ γ := Real.rpow_nonneg (by linarith [ht.2]) _
    have hh := hω t ht
    linarith
  have hcond := sourceBridge_curved_conditional_identity hReflection hReverse
    (d - H) H q b γ hT hq0 hbq hγ
  have hhalf := hsurv H d q b hH hd hq hb
  have hsum : H + (d - H) = d := by ring
  rw [hsum] at hcond
  rw [← hcond] at hhalf
  have hlaw : positiveBridgeCoefficientLaw (d - H) q (q - b) =
      ProbabilityTheory.cond gaussianCoefficientLaw (bridgeFlatEvent (d - H) b q) := by
    simp only [positiveBridgeCoefficientLaw, sub_sub_cancel]
  rw [hlaw] at hhalf
  have hmul := conditional_real_mul_of_subset gaussianCoefficientLaw
    (bridgeFlatEvent (d - H) b q) (bridgeCurvedEvent (d - H) b q d γ)
    (bridgeFlatEvent_nullMeasurable _ _ _) hmass hsubset
  constructor
  · have hh := mul_le_mul_of_nonneg_right hhalf hmass.le
    rw [hmul] at hh
    calc
      _ = (1 / 2 : ℝ) * (q * Real.sqrt H / d) := by ring
      _ ≤ (1 / 2 : ℝ) * gaussianCoefficientLaw.real (bridgeFlatEvent (d - H) b q) :=
        mul_le_mul_of_nonneg_left hflat.1 (by norm_num)
      _ ≤ _ := hh
  · exact (measureReal_mono hsubset (measure_ne_top _ _)).trans hflat.2

end SRWTightness
