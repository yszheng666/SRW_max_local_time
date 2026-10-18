import SRWTightness.SourceTerminalMarkProbability

open MeasureTheory Filter
namespace SRWTightness

/-- Internally constructed terminal bounds retaining the chosen observation radius. -/
def SourceTerminalEstimate (J A γ : ℝ) : Prop :=
    ∃ c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
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
            C * (Real.exp (-2 * d - 2 * q) / d)

/-- The existing terminal estimate supplies a shared radius certificate at every margin. -/
theorem source_terminal_estimate_exists (J : ℝ) (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A : ℝ, SourceTerminalEstimate J A γ := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_terminal_mark_probability_large_with_margin J hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hlog, hc, hC, hp⟩

end SRWTightness
