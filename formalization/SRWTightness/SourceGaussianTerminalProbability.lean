import SRWTightness.SourceTerminalGaussianLaw
import SRWTightness.TerminalProductUniformProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Uniform terminal bounds for the source K-Gaussian event with explicit scale hypotheses. -/
theorem sourceGaussian_terminal_probability (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput) (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (Cm γ : ℝ)
    (hMoment : BesselThreeInverseMomentInput Cm) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ Hmax ε K D : ℝ,
      H₀ ≤ Hmax → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ t A : ℝ, diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      ∀ I : ℕ, (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ d q At : ℝ,
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      let m := fun i : Fin ((I + 1) + 1) ↦ 2 * T (i.val + 1)
      let ν := (gaussianMeanCoordinateLaw m (brownianTimeMatrix T ((I + 1) + 1))).prod
        (independentBridgeLaw ℕ)
      H ∈ Set.Icc H₀ Hmax → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |T (I + 2) - d| ≤ K →
      T (I + 2) - T (I + 1) ∈ Set.Icc 1 D →
      c / d ≤ ν.real (sourceTerminalBridgeEvent t A I At q (Real.sqrt H) d γ) ∧
      ν.real (sourceTerminalBridgeEvent t A I At q (Real.sqrt H) d γ) ≤ C / d := by
  obtain ⟨H₀, hH₀, hp⟩ := terminal_product_probability_uniform hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro Hmax ε K D hmax hε hK hD
  obtain ⟨c, C, hc, hC, hb⟩ := hp Hmax ε K D hmax hε hK hD
  refine ⟨c, C, hc, hC, ?_⟩
  intro t A hA ht I hI d q At
  dsimp only
  intro hH hd hq hAt hV hΔ
  have hh := hb (d - sourceObservationTime t A I (I + 1)) d q At
    (sourceObservationTime t A I (I + 2))
    (sourceObservationTime t A I (I + 2) - sourceObservationTime t A I (I + 1))
    hH hd hq hAt hV hΔ
  dsimp only at hh
  have he : d - (d - sourceObservationTime t A I (I + 1)) =
      sourceObservationTime t A I (I + 1) := by ring
  rw [he] at hh
  rw [sourceTerminalBridgeEvent_gaussian_probability hReconstruct t A hA ht I hI]
  exact hh

end SRWTightness
