import SRWTightness.SourceTerminalTiltedProbability
import SRWTightness.SourceInverseTiltProbabilityAux
import SRWTightness.TerminalObservationPreimage

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Original mark-and-bridge terminal probability bounds after inverse site tilt. -/
theorem source_terminal_original_probability_large_with_margin (J : ℝ) (hReconstruct : BrownianBridgeReconstructionInput)
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
        let E := sourceTerminalBridgeEvent t A I (sourceTerminalThreshold t u)
          q (Real.sqrt H) d γ
        let Epre := (fun p ↦ ((fun i ↦ F i p.1), p.2)) ⁻¹' E
        c * Real.exp (-2 * d - 2 * q) / d ≤
          (μ.prod (independentBridgeLaw ℕ)).real Epre ∧
        (μ.prod (independentBridgeLaw ℕ)).real Epre ≤
          C * Real.exp (-2 * d - 2 * q) / d := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ := source_terminal_tilted_probability_large_with_margin J
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, Real.exp (-sourceInverseTiltExponentConstant) * c,
    Real.exp sourceInverseTiltExponentConstant * C, hA, hlog, by positivity, by positivity, ?_⟩
  filter_upwards [hp, source_inverse_tilt_probability_aux hBE A hA] with t hprob hinverse
  intro b
  obtain ⟨I, hI, z, hz, ht⟩ := hprob b
  obtain ⟨J, hJ, z', hz', hi⟩ := hinverse b
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hzz : z' = z := Subtype.ext (hz'.trans hz.symm)
  subst z'
  refine ⟨I, hI, z, hz, ?_⟩
  intro k q
  dsimp only
  intro hq hk
  let d := sourceLowerTime (sourceLowerRadius t)
  let u := sourceTerminalRoot t q
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let F := fun Y : MarkSamples M k ↦ fun i : Fin ((I + 1) + 1) ↦
    normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
      z k α (2 / Real.pi) u (diskObservationIndex (I + 1) i) Y
  let μ := markProductLaw D M α k
  let ρ := μ.tilted (fun Y ↦ 2 * normalizedMarkSum M k α (2 / Real.pi) u z Y)
  let E := sourceTerminalBridgeEvent t A I (sourceTerminalThreshold t u) q
    (Real.sqrt (d - sourceObservationTime t A I (I + 1))) d γ
  let Epre := (fun p : MarkSamples M k × (ℕ → GaussianCoefficientSpace) ↦
    (F p.1, p.2)) ⁻¹' E
  have htilt := ht k q hq hk
  letI : IsProbabilityMeasure ρ := htilt.1
  have hevent : MeasurableSet E := sourceTerminalBridgeEvent_measurable _ _ _ _ _ _ _ _
  have hpre : MeasurableSet Epre := hevent.preimage
    ((measurable_of_countable F).prodMap measurable_id)
  have hwindow : ∀ p ∈ Epre, sourceTerminalThreshold t u ≤
      normalizedMarkSum M k α (2 / Real.pi) u z p.1 ∧
      normalizedMarkSum M k α (2 / Real.pi) u z p.1 ≤ sourceTerminalThreshold t u + 1 := by
    intro p hp
    exact terminal_observation_preimage_window t A _ q _ d γ D M
      (geometricDiskFamily b A diskEnergyGapRatio (I + 1)) z k α (2 / Real.pi) u p hp
  have hinv := hi q hq.1 hq.2 k hk (ℕ → GaussianCoefficientSpace)
    (independentBridgeLaw ℕ) Epre hpre hwindow
  have hmap := terminal_observation_preimage_probability ρ t A I F
    (sourceTerminalThreshold t u) q
    (Real.sqrt (d - sourceObservationTime t A I (I + 1))) d γ
  have hb : c / d ≤ (ρ.prod (independentBridgeLaw ℕ)).real Epre ∧
      (ρ.prod (independentBridgeLaw ℕ)).real Epre ≤ C / d := by
    rw [← hmap]
    exact htilt.2
  change (Real.exp (-sourceInverseTiltExponentConstant) * c) *
      Real.exp (-2 * d - 2 * q) / d ≤ (μ.prod (independentBridgeLaw ℕ)).real Epre ∧
    (μ.prod (independentBridgeLaw ℕ)).real Epre ≤
      (Real.exp sourceInverseTiltExponentConstant * C) * Real.exp (-2 * d - 2 * q) / d
  constructor
  · calc
      _ = (Real.exp (-sourceInverseTiltExponentConstant) * Real.exp (-2 * d - 2 * q)) *
          (c / d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb.1
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ ≤ _ := hinv.1
  · calc
      _ ≤ _ := hinv.2
      _ ≤ (Real.exp sourceInverseTiltExponentConstant * Real.exp (-2 * d - 2 * q)) *
          (C / d) := mul_le_mul_of_nonneg_left hb.2
            (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = _ := by ring


/-- Original mark-and-bridge terminal probability bounds after inverse site tilt. -/
theorem source_terminal_original_probability_large (hReconstruct : BrownianBridgeReconstructionInput)
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
        let E := sourceTerminalBridgeEvent t A I (sourceTerminalThreshold t u)
          q (Real.sqrt H) d γ
        let Epre := (fun p ↦ ((fun i ↦ F i p.1), p.2)) ⁻¹' E
        c * Real.exp (-2 * d - 2 * q) / d ≤
          (μ.prod (independentBridgeLaw ℕ)).real Epre ∧
        (μ.prod (independentBridgeLaw ℕ)).real Epre ≤
          C * Real.exp (-2 * d - 2 * q) / d := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_terminal_original_probability_large_with_margin 0 hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
