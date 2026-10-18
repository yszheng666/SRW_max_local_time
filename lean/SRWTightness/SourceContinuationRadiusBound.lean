import SRWTightness.SourceContinuationUpperBound
import SRWTightness.ContinuationRadiusIdentity

open Filter MeasureTheory
namespace SRWTightness

/-- Literal source equation (7.30) with radius R=exp(t). -/
theorem source_continuation_radius_upper_bound (hGW : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ ν k : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
        Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν →
        sourceContinuationProbability t A γ b I z ν k ≤
          C * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) / (Real.exp t) ^ 2 *
            Real.exp (-2 * ν + 2 * Real.sqrt (2 * (k : ℝ))) := by
  obtain ⟨A, C, hA, hC, hp⟩ := source_continuation_upper_bound hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, C, hA, hC, ?_⟩
  filter_upwards [hp] with t hp
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := hp b
  refine ⟨I, hI, z, hz, ?_⟩
  intro ν k hν hx
  have hh := hb ν k hν hx
  rw [continuation_radius_decay_identity] at hh
  convert hh using 1 <;> ring

end SRWTightness
