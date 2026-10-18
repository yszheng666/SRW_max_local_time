import SRWTightness.SourceContinuationFirstUpper
import SRWTightness.SourceContinuationDecay

open Filter MeasureTheory
namespace SRWTightness

/-- Equation (7.30), with R=exp(t), for the actual reference continuation probability. -/
theorem source_continuation_upper_bound (hGW : GWBarrierUpperInput)
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
          C * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) *
            Real.exp (-2 * t - 2 * ν + 2 * Real.sqrt (2 * (k : ℝ))) := by
  obtain ⟨A, C, hA, hC, hp⟩ := source_continuation_first_upper hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  obtain ⟨D, hD, hd⟩ := source_continuation_decay
  refine ⟨A, C * D, hA, by positivity, ?_⟩
  filter_upwards [hp, hd] with t hp hd
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := hp b
  refine ⟨I, hI, z, hz, ?_⟩
  intro ν k hν hx
  let x := Real.sqrt (2 * (k : ℝ))
  let F := ((ν : ℝ) + 1) * Real.sqrt x / t ^ 2 *
    Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
    Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
      (2 * ((sourceCoarseGeneration t : ℝ) - ν))))
  have hfirst : sourceContinuationProbability t A γ b I z ν k ≤ C * F := by
    convert hb ν k hν hx using 1 <;> dsimp [F, x] <;> ring
  have hdecay : F ≤ D * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) *
      Real.exp (-2 * t - 2 * ν + 2 * x) := hd ν x hν (Real.sqrt_nonneg _) hx
  calc
    _ ≤ C * F := hfirst
    _ ≤ C * (D * ((ν : ℝ) + 1) ^ (3 / 2 : ℝ) *
        Real.exp (-2 * t - 2 * ν + 2 * x)) := mul_le_mul_of_nonneg_left hdecay hC.le
    _ = _ := by ring

end SRWTightness
