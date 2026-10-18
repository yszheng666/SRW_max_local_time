import SRWTightness.GaussianGridTerminalProbability
import SRWTightness.SourceTerminalApplicationConditions

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Actual source windows have K-Gaussian terminal probability of order 1/d at large times. -/
theorem source_terminal_K_probability_large (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C t₀ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < c ∧ 0 < C ∧
      ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (I : ℕ),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ q : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      let At := sourceTerminalThreshold t (sourceTerminalRoot t q)
      let V := sourcePointEnergyTime b (sourceLowerRadius t) 14
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      let μ := (gaussianCoordinateLaw (brownianTimeMatrix T ((I + 1) + 1))).prod
        (independentBridgeLaw ℕ)
      let E := gaussianGridTerminalEvent T (I + 1) (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      c / d ≤ μ.real E ∧ μ.real E ≤ C / d := by
  obtain ⟨H₀, hH₀, hp⟩ := gaussianGrid_terminal_probability_uniform hReconstruct hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  obtain ⟨A, Hmax, D, t₀, hA, hmax, hD, ha⟩ :=
    source_terminal_application_conditions H₀ 1 (by norm_num)
  let K := max 0 (sourcePointEnergyTimeError + sourceLowerTimeError)
  obtain ⟨c, C, hc, hC, hb⟩ := hp Hmax 1 K D hmax (by norm_num) (le_max_left _ _) hD
  refine ⟨A, c, C, t₀, hA, hc, hC, ?_⟩
  intro t ht b I hI q
  dsimp only
  intro hq
  have hs := ha t ht b I hI q hq
  exact hb (sourceObservationTime t A I) (I + 1) (by omega)
    (sourceObservationTime_zero t A I)
    (sourceObservationTime_gaps t A hA hs.1 I hI)
    (sourceLowerTime (sourceLowerRadius t)) q
    (sourceTerminalThreshold t (sourceTerminalRoot t q))
    (sourcePointEnergyTime b (sourceLowerRadius t) 14)
    hs.2.1 hs.2.2.1 hq hs.2.2.2.2.1
    (hs.2.2.2.2.2.trans (le_max_right _ _))
    (by simpa only [Nat.add_assoc] using hs.2.2.2.1)

end SRWTightness
