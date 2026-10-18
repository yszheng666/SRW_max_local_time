import SRWTightness.SourceTerminalMarkProbability
import SRWTightness.SourceTerminalContinuousProbabilityReconstructed

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_terminal_mark_probability_large_with_margin_reconstructed (J : ℝ)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ t : ℝ in Filter.atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ (L : ℕ) (r : GeometricGWRecord),
        let d := sourceLowerTime (sourceLowerRadius t)
        let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
        q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
        c * (Real.exp (-2 * d - 2 * q) / d) ≤
            sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L) ∧
          sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L) ≤
            C * (Real.exp (-2 * d - 2 * q) / d) := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_terminal_continuous_probability_large_with_margin_reconstructed J
    hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [hp] with t ht
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := ht b
  refine ⟨I, hI, z, hz, ?_⟩
  intro L r
  dsimp only
  intro hq
  have hid := source_gw_terminal_count_identity t L r
  dsimp only at hid
  have hh := hb (geometricGWPopulation r L)
    (sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L) hq hid.2
  dsimp only at hh
  rw [hid.1] at hh
  simpa only [sourceTerminalMarkProbability, geometricGWHeight, mul_div_assoc] using hh

end SRWTightness
