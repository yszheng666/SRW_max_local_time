import SRWTightness.SourceTerminalBridgeEvent
import SRWTightness.SourceSiteTiltApproximation

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

namespace SRWTightness

/-- The actual source terminal bridge event satisfies the tilted Gaussian comparison. -/
theorem source_terminal_bridge_comparison
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (A : ℝ) (hA : diskPointGaussianMinimumRadius ≤ A) :
    ∀ᶠ t : ℝ in atTop, ∀ b : Site, ∃ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      let R := Real.exp 1 * sourceLowerRadius t + 14
      let α := sourceReferenceIntensity (sourceLowerRadius t) 14
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let D := translateFinset b (diskFinset R)
      ∃ z : M, (z : Site) = b ∧ ∀ (k : ℕ) (u : ℝ), t ≤ u → u ^ 2 / 2 = (k : ℝ) →
        let F := fun i : Fin ((I + 1) + 1) ↦
          normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
            z k α (2 / Real.pi) u (diskObservationIndex (I + 1) i)
        let μ := markProductLaw D M α k
        let ρ := μ.tilted (fun Y ↦ 2 * normalizedMarkSum M k α (2 / Real.pi) u z Y)
        let Sigma : Matrix (Fin ((I + 1) + 1)) (Fin ((I + 1) + 1)) ℝ :=
          fun i j ↦ covariance (F i) (F j) μ
        let target := fun i : Fin ((I + 1) + 1) ↦
          2 * geometricDiskPointTime R A diskEnergyGapRatio α (I + 1) (i.val + 1)
        IsProbabilityMeasure ρ ∧ Sigma.PosDef ∧
        ∀ (At q aStar d γ : ℝ),
          let E := sourceTerminalBridgeEvent t A I At q aStar d γ
          |((ρ.map (fun Y i ↦ F i Y)).prod (independentBridgeLaw ℕ)).real E -
            ((gaussianMeanCoordinateLaw target Sigma).prod (independentBridgeLaw ℕ)).real E| ≤
              sourceSiteTiltError t := by
  filter_upwards [source_site_tilt_approximation hBE A hA] with t ht
  intro b
  obtain ⟨I, hI, z, hz, happ⟩ := ht b
  refine ⟨I, hI, z, hz, ?_⟩
  intro k u hu hk
  obtain ⟨hprob, hpos, _, haux⟩ := happ k u hu hk
  refine ⟨hprob, hpos, ?_⟩
  intro At q aStar d γ
  exact haux (ℕ → GaussianCoefficientSpace) (independentBridgeLaw ℕ)
    (sourceTerminalBridgeEvent t A I At q aStar d γ)
    (sourceTerminalBridgeEvent_measurable t A I At q aStar d γ)
    (Filter.Eventually.of_forall (sourceTerminalBridgeEvent_convex t A I At q aStar d γ))

end SRWTightness
