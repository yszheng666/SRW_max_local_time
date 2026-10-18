import SRWTightness.GaussianGridBridgeEventLaw
import SRWTightness.SourceEndpointBridgeProbability
import SRWTightness.SourceGaussianGridPath

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The source average-window and curve event has order sqrt(H)/d under its actual K-Gaussian law. -/
theorem sourceGaussian_curve_probability (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput) (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (Cm γ : ℝ)
    (hMoment : BesselThreeInverseMomentInput Cm) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ c C : ℝ, 1 ≤ H₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ t A : ℝ, diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      ∀ I : ℕ, (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ d q : ℝ,
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      let ν := (gaussianCoordinateLaw (brownianTimeMatrix T ((I + 1) + 1))).prod
        (independentBridgeLaw ℕ)
      H₀ ≤ H → 256 * H ≤ d → q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      c * Real.sqrt H / d ≤ ν.real
        (gaussianGridEndpointCurveEvent T (I + 1)
          (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ) ∧
      ν.real (gaussianGridEndpointCurveEvent T (I + 1)
          (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ) ≤ C * Real.sqrt H / d := by
  obtain ⟨H₀, c, C, hH₀, hc, hC, hp⟩ := source_endpoint_bridge_probability hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  refine ⟨H₀, c, C, hH₀, hc, hC, ?_⟩
  intro t A hA ht I hI d q
  dsimp only
  intro hH hd hq
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hprob := hp (d - sourceObservationTime t A I (I + 1)) d q hH hd hq
  have he : d - (d - sourceObservationTime t A I (I + 1)) =
      sourceObservationTime t A I (I + 1) := by ring
  rw [he] at hprob
  rw [gaussianGrid_endpoint_curve_probability hReconstruct _ _ (by omega)
    (sourceObservationTime_zero t A I) hg]
  exact hprob

end SRWTightness
