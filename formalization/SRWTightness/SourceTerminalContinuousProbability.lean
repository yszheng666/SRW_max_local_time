import SRWTightness.SourceTerminalOriginalProbability
import SRWTightness.SourceTerminalContinuousEvent

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Conditional certification of the original continuous terminal event probability scale. -/
theorem source_terminal_continuous_probability_large_with_margin (J : ℝ) (hReconstruct : BrownianBridgeReconstructionInput)
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
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let D := translateFinset b (diskFinset R)
      ∃ z : M, (z : Site) = b ∧ ∀ (k : ℕ) (q : ℝ),
        let d := sourceLowerTime (sourceLowerRadius t)
        q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
        let u := sourceTerminalRoot t q
        u ^ 2 / 2 = (k : ℝ) →
        let F := fun i : Fin ((I + 1) + 1) ↦
          normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
            z k α (2 / Real.pi) u (diskObservationIndex (I + 1) i)
        let μ := markProductLaw D M α k
        let H := d - sourceObservationTime t A I (I + 1)
        let E := sourceTerminalContinuousEvent t A I (sourceTerminalThreshold t u)
          q (Real.sqrt H) d γ
        let Epre := (fun p ↦ ((fun i ↦ F i p.1), p.2)) ⁻¹' E
        c * Real.exp (-2 * d - 2 * q) / d ≤
          (μ.prod (independentBridgeLaw ℕ)).real Epre ∧
        (μ.prod (independentBridgeLaw ℕ)).real Epre ≤
          C * Real.exp (-2 * d - 2 * q) / d := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ := source_terminal_original_probability_large_with_margin J
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [hp] with t ht
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := ht b
  refine ⟨I, hI, z, hz, ?_⟩
  intro k q
  dsimp only
  intro hq hk
  have hh := hb k q hq hk
  dsimp only at hh
  let F := fun Y : MarkSamples (translateFinset b (diskFinset
      (A * diskEnergyGapRatio ^ I))) k ↦ fun i : Fin ((I + 1) + 1) ↦
    normalizedObservation (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
      (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
      (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
      (sourceTerminalRoot t q) (diskObservationIndex (I + 1) i) Y
  rw [source_terminal_continuous_preimage_probability _ t A I F
    (sourceTerminalThreshold t (sourceTerminalRoot t q)) q
    (Real.sqrt (sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I + 1)))
    (sourceLowerTime (sourceLowerRadius t)) γ hγ] at hh
  exact hh


/-- Conditional certification of the original continuous terminal event probability scale. -/
theorem source_terminal_continuous_probability_large (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < c ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let D := translateFinset b (diskFinset R)
      ∃ z : M, (z : Site) = b ∧ ∀ (k : ℕ) (q : ℝ),
        let d := sourceLowerTime (sourceLowerRadius t)
        q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
        let u := sourceTerminalRoot t q
        u ^ 2 / 2 = (k : ℝ) →
        let F := fun i : Fin ((I + 1) + 1) ↦
          normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
            z k α (2 / Real.pi) u (diskObservationIndex (I + 1) i)
        let μ := markProductLaw D M α k
        let H := d - sourceObservationTime t A I (I + 1)
        let E := sourceTerminalContinuousEvent t A I (sourceTerminalThreshold t u)
          q (Real.sqrt H) d γ
        let Epre := (fun p ↦ ((fun i ↦ F i p.1), p.2)) ⁻¹' E
        c * Real.exp (-2 * d - 2 * q) / d ≤
          (μ.prod (independentBridgeLaw ℕ)).real Epre ∧
        (μ.prod (independentBridgeLaw ℕ)).real Epre ≤
          C * Real.exp (-2 * d - 2 * q) / d := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_terminal_continuous_probability_large_with_margin 0 hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
