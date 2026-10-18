import SRWTightness.SourceSiteTiltApproximation
import SRWTightness.SourceTerminalBridgeEvent

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology

namespace SRWTightness

/-- The actual terminal event satisfies the tilted-law CLT with its exact source covariance. -/
theorem source_site_tilt_terminal_approximation
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
          brownianTimeMatrix (sourceObservationTime t A I) ((I + 1) + 1) -
            Matrix.diagonal (geometricDiskPointError b A R diskEnergyGapRatio (2 / Real.pi) (I + 1))
        let target := fun i : Fin ((I + 1) + 1) ↦
          2 * geometricDiskPointTime R A diskEnergyGapRatio α (I + 1) (i.val + 1)
        IsProbabilityMeasure ρ ∧ Sigma.PosDef ∧
        ∀ At q aStar d γ : ℝ,
          let E := sourceTerminalBridgeEvent t A I At q aStar d γ
          |((ρ.map (fun Y i ↦ F i Y)).prod (independentBridgeLaw ℕ)).real E -
            ((gaussianMeanCoordinateLaw target Sigma).prod (independentBridgeLaw ℕ)).real E| ≤
            sourceSiteTiltError t := by
  filter_upwards [source_site_tilt_approximation hBE A hA,
    eventually_ge_atTop (sourceGaussianThreshold A)] with t happ ht
  intro b
  obtain ⟨I, hI, z, hz, hp⟩ := happ b
  obtain ⟨J, hJ, z', hz', hcov⟩ := source_observation_covariance b t A hA ht
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hzz : z' = z := Subtype.ext (hz'.trans hz.symm)
  subst z'
  refine ⟨I, hI, z, hz, ?_⟩
  intro k u hu hk
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have ht2 := (sourceScaleThreshold_conditions t A ha4 ((le_max_left _ _).trans ht)).1
  have hu0 : 0 < u := by linarith
  have hh := hp k u hu hk
  dsimp only at hh ⊢
  simp_rw [hcov k u hu0 hk] at hh
  refine ⟨hh.1, hh.2.1, ?_⟩
  intro At q aStar d γ
  exact hh.2.2.2 (ℕ → GaussianCoefficientSpace) (independentBridgeLaw ℕ)
    (sourceTerminalBridgeEvent t A I At q aStar d γ)
    (sourceTerminalBridgeEvent_measurable _ _ _ _ _ _ _ _)
    (Filter.Eventually.of_forall (sourceTerminalBridgeEvent_convex _ _ _ _ _ _ _ _))

end SRWTightness
