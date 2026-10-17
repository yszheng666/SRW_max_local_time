import SRWTightness.SourceTerminalMarkProbability
import SRWTightness.SourceTerminalWindowSum

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Uniform source terminal bounds integrated over any coarse window restricted to the true band. -/
theorem source_terminal_mark_window_integral_with_margin (J : ℝ) (hReconstruct : BrownianBridgeReconstructionInput)
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
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ (L : ℕ) (q : ℝ) (S : Set GeometricGWRecord),
        S ⊆ sourceGWCoarseWindowEvent t L q →
        (∀ r ∈ S, sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L ∈
          Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
            (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))) →
        let d := sourceLowerTime (sourceLowerRadius t)
        let μ := geometricGWRecordLaw 1 L
        let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
        (c * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S ≤ ∫ r in S, P r ∂μ ∧
          (∫ r in S, P r ∂μ) ≤
            (C * Real.exp 2 * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ := source_terminal_mark_probability_large_with_margin J
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [hp, eventually_ge_atTop (sourceGaussianThreshold A),
    eventually_ge_atTop (sourceScaleThreshold 4), source_lower_time_eventually_ge 1]
    with t hp htA ht4 hd
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
  intro L q S hS hband
  apply source_gw_window_integral_bounds t L q c C _ S (by linarith) hc.le hC.le
  · intro r
    exact source_terminal_mark_probability_mem t A γ b I z _ hα.le hcap
  · exact hS
  · intro r hr
    exact hb L r (hband r hr)


/-- Uniform source terminal bounds integrated over any coarse window restricted to the true band. -/
theorem source_terminal_mark_window_integral (hReconstruct : BrownianBridgeReconstructionInput)
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
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)),
        (z : Site) = b ∧ ∀ (L : ℕ) (q : ℝ) (S : Set GeometricGWRecord),
        S ⊆ sourceGWCoarseWindowEvent t L q →
        (∀ r ∈ S, sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L ∈
          Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
            (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))) →
        let d := sourceLowerTime (sourceLowerRadius t)
        let μ := geometricGWRecordLaw 1 L
        let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
        (c * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S ≤ ∫ r in S, P r ∂μ ∧
          (∫ r in S, P r ∂μ) ≤
            (C * Real.exp 2 * (Real.exp (-2 * d - 2 * q) / d)) * μ.real S := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_terminal_mark_window_integral_with_margin 0 hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
