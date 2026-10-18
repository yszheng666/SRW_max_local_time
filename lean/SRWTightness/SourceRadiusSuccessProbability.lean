import SRWTightness.SourceLocalTimeSuccessProbability

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The original-event probability bound holds for every sufficiently large real radius. -/
theorem source_local_time_success_probability_radius_with_margin (J : ℝ) (hPotential : PotentialKernelAsymptoticInput)
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
      ∀ᶠ R : ℝ in atTop, ∀ b : Site,
      R / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ R / 3 →
      ∃ I : ℕ,
        (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)), (z : Site) = b ∧
      ∀ [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      c * (R ^ 2)⁻¹ ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent (Real.log R) A γ b I z) ∧
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent (Real.log R) A γ b I z) ≤ C * (R ^ 2)⁻¹ := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hb⟩ := source_local_time_success_probability_with_margin J
    hPotential hLower hUpper hReconstruct hBE hGaussian hReflection hBridge hReverse
    hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, c, C, hA, hlog, hc, hC, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hb, eventually_gt_atTop (0 : ℝ)]
    with R hlarge hR
  have he : Real.exp (-2 * Real.log R) = (R ^ 2)⁻¹ := by
    rw [show -2 * Real.log R = -(Real.log R + Real.log R) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log hR, pow_two]
  simpa only [Real.exp_log hR, he] using hlarge


/-- The original-event probability bound holds for every sufficiently large real radius. -/
theorem source_local_time_success_probability_radius (hPotential : PotentialKernelAsymptoticInput)
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
      ∀ᶠ R : ℝ in atTop, ∀ b : Site,
      R / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ R / 3 →
      ∃ I : ℕ,
        (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I) ∧
      ∃ z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)), (z : Site) = b ∧
      ∀ [MeasurableSpace (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))]
        [MeasurableSingletonClass (List (Mark (translateFinset b
          (diskFinset (A * diskEnergyGapRatio ^ I)))))],
      MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
      c * (R ^ 2)⁻¹ ≤ (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent (Real.log R) A γ b I z) ∧
        (pathLaw.prod (independentBridgeLaw ℕ)).real
          (sourceLocalTimeSuccessEvent (Real.log R) A γ b I z) ≤ C * (R ^ 2)⁻¹ := by
  obtain ⟨A, c, C, hA, hlog, hc, hC, hp⟩ :=
    source_local_time_success_probability_radius_with_margin 0 hPotential hLower hUpper hReconstruct hBE hGaussian
      hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  exact ⟨A, c, C, hA, hc, hC, hp⟩

end SRWTightness
