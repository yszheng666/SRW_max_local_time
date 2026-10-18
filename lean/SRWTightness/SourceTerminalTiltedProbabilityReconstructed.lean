import SRWTightness.SourceTerminalTiltedProbability
import SRWTightness.SourceTerminalMeanSigmaProbabilityReconstructed

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_terminal_tilted_probability_large_with_margin_reconstructed (J : ℝ)
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
        let ρ := μ.tilted (fun Y ↦ 2 * normalizedMarkSum M k α (2 / Real.pi) u z Y)
        let H := d - sourceObservationTime t A I (I + 1)
        let E := sourceTerminalBridgeEvent t A I (sourceTerminalThreshold t u)
          q (Real.sqrt H) d γ
        IsProbabilityMeasure ρ ∧
        c / d ≤ ((ρ.map (fun Y i ↦ F i Y)).prod (independentBridgeLaw ℕ)).real E ∧
        ((ρ.map (fun Y i ↦ F i Y)).prod (independentBridgeLaw ℕ)).real E ≤ C / d := by
  obtain ⟨A, c, C, tg, hA, hlog, hc, hC, hg⟩ :=
    source_terminal_mean_sigma_probability_large_with_margin_reconstructed J
    hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  obtain ⟨te, he⟩ := source_terminal_CLT_absorption c C hc
  refine ⟨A, c / 2, C + c / 2, hA, hlog, by positivity, by positivity, ?_⟩
  filter_upwards [source_site_tilt_terminal_approximation hBE A hA,
    eventually_ge_atTop tg, eventually_ge_atTop te, source_deficit_large_conditions]
    with t happ htG htE ht
  intro b
  obtain ⟨I, hI, z, hz, hp⟩ := happ b
  refine ⟨I, hI, z, hz, ?_⟩
  intro k q
  dsimp only
  intro hq hk
  have hu := sourceTerminalRoot_bounds t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hq.1 hq.2
  have hclt := hp k (sourceTerminalRoot t q) hu.1 hk
  have hgauss := hg t htG b I hI q hq
  have herr := hclt.2.2 (sourceTerminalThreshold t (sourceTerminalRoot t q)) q
    (Real.sqrt (sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I + 1)))
    (sourceLowerTime (sourceLowerRadius t)) γ
  exact ⟨hclt.1, he t htE _ _ hgauss.1 hgauss.2 herr⟩

end SRWTightness
