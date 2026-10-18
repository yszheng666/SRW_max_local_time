import SRWTightness.SourceWalkSuccessIdentification

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Uniform one-point probability bounds for the original local-time continuous success event. -/
theorem source_local_time_success_probability_with_margin (J : ℝ) (hPotential : PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
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
      ∀ᶠ t : ℝ in atTop, ∀ b : Site,
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∃ I : ℕ,
        (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)), (z : Site) = b ∧
      ∀ [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      c * Real.exp (-2 * t) ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent t A γ b I z) ∧
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent t A γ b I z) ≤ C * Real.exp (-2 * t) := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hb⟩ := source_record_success_probability_with_margin J
    hPotential hLower hUpper hReconstruct hBE hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [hb, source_walk_success_probability_identification] with t ht heq
  intro b hblo hbhi
  obtain ⟨I, hI, z, hz, hbounds⟩ := ht b hblo hbhi
  refine ⟨I, hI, z, hz, ?_⟩
  intro instM instMS hjoint
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hpow : 1 ≤ diskEnergyGapRatio ^ I :=
    one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  have ha : 1 ≤ A * diskEnergyGapRatio ^ I := by nlinarith
  rw [← heq A γ b I z hγ ha ((hI I).mpr le_rfl) hblo hbhi]
  exact hbounds hjoint


/-- Uniform one-point probability bounds for the original local-time continuous success event. -/
theorem source_local_time_success_probability (hPotential : PotentialKernelAsymptoticInput)
    (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput)
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
      ∀ᶠ t : ℝ in atTop, ∀ b : Site,
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∃ I : ℕ,
        (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)), (z : Site) = b ∧
      ∀ [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      c * Real.exp (-2 * t) ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent t A γ b I z) ∧
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent t A γ b I z) ≤ C * Real.exp (-2 * t) := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_local_time_success_probability_with_margin 0 hPotential hLower hUpper hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
