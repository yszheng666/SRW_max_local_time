import SRWTightness.SourceMarkedWindowWeight
import SRWTightness.SourceGWBandScale

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Conditional reference success estimate after summing the entire terminal deficit band. -/
theorem source_marked_reference_success_with_margin (J : ℝ) (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
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
        (z : Site) = b ∧
        let L := (sourceCoarseGeneration t).toNat
        let μ := geometricGWRecordLaw 1 L
        let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
        c * Real.exp (-2 * t) ≤ (∫ r in sourceGWCoarseBandEvent t L, P r ∂μ) ∧
          (∫ r in sourceGWCoarseBandEvent t L, P r ∂μ) ≤ C * Real.exp (-2 * t) := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ := source_marked_window_weight_with_margin J hLower hUpper
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, c / 2, 9 * C, hA, hlog, by positivity, by positivity, ?_⟩
  filter_upwards [hp, source_lower_time_eventually_ge 4] with t ht hd
  intro b
  obtain ⟨I, hI, z, hz, hPi, hP0, hw⟩ := ht b
  refine ⟨I, hI, z, hz, ?_⟩
  exact source_gw_band_integral_scale t _ c C _ hc.le hC.le hd hPi hP0 hw


/-- Conditional reference success estimate after summing the entire terminal deficit band. -/
theorem source_marked_reference_success (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
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
        (z : Site) = b ∧
        let L := (sourceCoarseGeneration t).toNat
        let μ := geometricGWRecordLaw 1 L
        let P := fun r ↦ sourceTerminalMarkProbability t A γ b I z (geometricGWPopulation r L)
        c * Real.exp (-2 * t) ≤ (∫ r in sourceGWCoarseBandEvent t L, P r ∂μ) ∧
          (∫ r in sourceGWCoarseBandEvent t L, P r ∂μ) ≤ C * Real.exp (-2 * t) := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_marked_reference_success_with_margin 0 hLower hUpper hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
