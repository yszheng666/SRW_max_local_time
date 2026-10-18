import SRWTightness.SourceTerminalContinuousProbability
import SRWTightness.SourceGWWindowIntegral
import SRWTightness.SourceGWTerminalCount

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The original terminal mark-and-bridge event probability at an integer terminal population. -/
noncomputable def sourceTerminalMarkProbability (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ) : ℝ :=
  let d := sourceLowerTime (sourceLowerRadius t)
  let D := translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let α := sourceReferenceIntensity (sourceLowerRadius t) 14
  let u := Real.sqrt (2 * (k : ℝ))
  let q := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - u
  let F := fun i : Fin ((I + 1) + 1) ↦
    normalizedObservation D M (geometricDiskFamily b A diskEnergyGapRatio (I + 1))
      z k α (2 / Real.pi) u (diskObservationIndex (I + 1) i)
  let H := d - sourceObservationTime t A I (I + 1)
  let E := sourceTerminalContinuousEvent t A I (sourceTerminalThreshold t u)
    q (Real.sqrt H) d γ
  ((markProductLaw D M α k).prod (independentBridgeLaw ℕ)).real
    ((fun p ↦ ((fun i ↦ F i p.1), p.2)) ⁻¹' E)

/-- Normalization of the actual mark law bounds the terminal success probability. -/
theorem source_terminal_mark_probability_mem (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) (k : ℕ)
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ≤ 1) :
    sourceTerminalMarkProbability t A γ b I z k ∈ Set.Icc (0 : ℝ) 1 := by
  letI := markProductLaw_isProbabilityMeasure _ _ _ hα hcap k
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- The terminal success probability, read at the actual GW population, is integrable. -/
theorem source_terminal_mark_probability_integrable (t A γ : ℝ) (b : Site) (I L : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
    (hcap : sourceReferenceIntensity (sourceLowerRadius t) 14 *
      capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ≤ 1) :
    Integrable (fun r ↦ sourceTerminalMarkProbability t A γ b I z
      (geometricGWPopulation r L)) (geometricGWRecordLaw 1 L) := by
  apply gw_record_probability_integrable
  intro r
  exact source_terminal_mark_probability_mem t A γ b I z _ hα hcap

/-- The source terminal estimate evaluated at the integer population in a GW record. -/
theorem source_terminal_mark_probability_large_with_margin (J : ℝ) (hReconstruct : BrownianBridgeReconstructionInput)
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
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ := source_terminal_continuous_probability_large_with_margin J
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
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


/-- The source terminal estimate evaluated at the integer population in a GW record. -/
theorem source_terminal_mark_probability_large (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < c ∧ 0 < C ∧
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
    source_terminal_mark_probability_large_with_margin 0 hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
