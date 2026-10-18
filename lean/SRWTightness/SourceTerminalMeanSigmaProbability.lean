import SRWTightness.SourceTerminalSigmaProbability
import SRWTightness.SourceTerminalCovarianceCentering

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The original source terminal event has two-sided bounds under its comparison Gaussian mean law. -/
theorem source_terminal_mean_sigma_probability_large_with_margin (J : ℝ) (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C t₀ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
      ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (I : ℕ),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ q : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      let At := sourceTerminalThreshold t (sourceTerminalRoot t q)
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      let e := geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
        diskEnergyGapRatio (2 / Real.pi) (I + 1)
      let m := fun i : Fin ((I + 1) + 1) ↦ 2 * T (i.val + 1)
      let μ := (gaussianMeanCoordinateLaw m
        (brownianTimeMatrix T ((I + 1) + 1) - Matrix.diagonal e)).prod
        (independentBridgeLaw ℕ)
      let E := sourceTerminalBridgeEvent t A I At q (Real.sqrt H) d γ
      c / d ≤ μ.real E ∧ μ.real E ≤ C / d := by
  obtain ⟨A, c, C, t₀, hA, hlog, hc, hC, hp⟩ := source_terminal_sigma_probability_large_with_margin J
    hReconstruct hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, c, C, max t₀ (sourceGaussianThreshold A), hA, hlog, hc, hC, ?_⟩
  intro t ht b I hI q
  dsimp only
  intro hq
  have htG := (le_max_right _ _).trans ht
  have hh := hp t ((le_max_left _ _).trans ht) b I hI q hq
  dsimp only at hh
  rw [sourceTerminalBridgeEvent_covariance_centering t A hA htG I hI]
  rw [sourceObservationTime_site b]
  exact hh


/-- The original source terminal event has two-sided bounds under its comparison Gaussian mean law. -/
theorem source_terminal_mean_sigma_probability_large (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C t₀ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < c ∧ 0 < C ∧
      ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (I : ℕ),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ q : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      let At := sourceTerminalThreshold t (sourceTerminalRoot t q)
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      let e := geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
        diskEnergyGapRatio (2 / Real.pi) (I + 1)
      let m := fun i : Fin ((I + 1) + 1) ↦ 2 * T (i.val + 1)
      let μ := (gaussianMeanCoordinateLaw m
        (brownianTimeMatrix T ((I + 1) + 1) - Matrix.diagonal e)).prod
        (independentBridgeLaw ℕ)
      let E := sourceTerminalBridgeEvent t A I At q (Real.sqrt H) d γ
      c / d ≤ μ.real E ∧ μ.real E ≤ C / d := by
  obtain ⟨A, c, C, t₀, hA, hlog, hc, hC, hp⟩ :=
    source_terminal_mean_sigma_probability_large_with_margin 0 hReconstruct hGaussian hReflection hBridge hReverse hPositive hInitial hHit
      Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, t₀, hA, hc, hC, hp⟩

end SRWTightness
