import SRWTightness.SourceContinuationWeightedBand
import SRWTightness.SourceContinuationProbability
import SRWTightness.SourceTerminalMarkWindow

open Filter MeasureTheory
namespace SRWTightness

/-- Equation (7.31) for the actual reference continuation probability and terminal marks. -/
theorem source_continuation_first_upper (hGW : GWBarrierUpperInput)
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
          C * ((ν : ℝ) + 1) * Real.sqrt (Real.sqrt (2 * (k : ℝ))) / t ^ 2 *
            Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
            Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
              Real.sqrt (2 * (k : ℝ))) ^ 2 /
                (2 * ((sourceCoarseGeneration t : ℝ) - ν)))) := by
  obtain ⟨G, hG, hg⟩ := source_continuation_weighted_band hGW
  obtain ⟨A, c, C, hA, hc, hC, hp⟩ := source_terminal_mark_probability_large
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, G * C, hA, by positivity, ?_⟩
  filter_upwards [hg, hp, source_continuation_length_eq,
    eventually_ge_atTop (sourceGaussianThreshold A),
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hg hp hlen htA ht4
  intro b
  obtain ⟨I, hI, z, hz, hb⟩ := hp b
  obtain ⟨J, hJ, hcap⟩ := source_reference_capacity b t A hA htA
  have hIJ : I = J := Nat.le_antisymm
    ((hJ I).mp ((hI I).mpr le_rfl)) ((hI J).mp ((hJ J).mpr le_rfl))
  subst J
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht4).2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1
  refine ⟨I, hI, z, hz, ?_⟩
  intro ν k hν hx
  by_cases hk : k = 0
  · simp [sourceContinuationProbability, hk]
  · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
    let L := sourceContinuationLength t ν
    have hL := hlen ν hν
    have hLreal : (L : ℝ) = (sourceCoarseGeneration t : ℝ) - ν := by
      dsimp [L]; linarith
    have hh := hg ν L k C
      (fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L))
      hν hL hk0 hx hC.le
      (fun r ↦ source_terminal_mark_probability_mem t A γ b I z _ hα.le hcap)
      (fun r hr ↦ (hb L r hr.2).2)
    unfold sourceContinuationProbability
    rw [if_neg hk]
    change (∫ r in sourceContinuationBand t ν L,
      sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
      ∂geometricGWRecordLaw k L) ≤ _
    rw [hLreal] at hh
    exact hh

end SRWTightness
