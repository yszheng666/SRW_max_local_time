import SRWTightness.SourceCompleteCappedPair
import SRWTightness.SourceFixedContinuationPair
import SRWTightness.SourceFixedDecouplingError
import SRWTightness.FixedPairScales
import SRWTightness.CappedProbabilityProduct

open MeasureTheory Filter
namespace SRWTightness

/-- Every bounded range of distance indices, including zero, has an inverse fourth-power
radius bound for the original two-site success events. -/
theorem source_fixed_pair_success_bound (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput)
    (hGW : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    :
    ∃ A : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ ∀ a₀ : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∃ ν : ℕ, ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) ≤ a₀ →
      ∃ I₀ I₁ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) ∧
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₁) ∧
      ∃ (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      (z₀ : Site) = b ∧ (z₁ : Site) = w ∧ ∀
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)),
      sourceEnlargedLaw.real
        (sourceSiteSuccessEvent t A γ b I₀ z₀ ∩ sourceSiteSuccessEvent t A γ w I₁ z₁) ≤
      C / (Real.exp t) ^ 4 := by
  obtain ⟨D, C₁, B, W, Jbar, hD, hC₁, hB, hW, hJbar, hbound⟩ :=
    source_complete_capped_pair_bound_all_indices hExt hFlat hR hP hH hM hT
  obtain ⟨A, C₀, hA, hC₀, hcont⟩ := source_continuation_pair_fixed_level_bound hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, hA, ?_⟩
  intro a₀
  let ν := a₀ + ⌈Jbar⌉₊ + 5
  let E := 16 * D * ((ν : ℝ) + 1) ^ 3 + 1
  let K := C₀ * ((ν : ℝ) + 1) ^ 3 * Real.exp (16 * ((ν : ℝ) + 1))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Real.exp E * K, mul_pos (Real.exp_pos _) hK, ν, ?_⟩
  filter_upwards [hbound, hcont, sourceCoarseLowerLevel_eventually_ge ν,
    source_fixed_decoupling_exponent_bounded D C₁ B W hD.le hC₁.le]
    with t ht hc hlevel he
  intro b w hb hw hbw ha
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := ν - a - 5
  have hgap := fixed_pair_level_gap a₀ ⌈Jbar⌉₊ a ha
  have hν : ν ≤ 2 * sourceCoarseLowerLevel t := by omega
  have hform : ν = a + J + 5 := hgap.1
  have hJ : Jbar ≤ (J : ℝ) := (Nat.le_ceil Jbar).trans (Nat.cast_le.mpr hgap.2.1)
  obtain ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, hprod⟩ := hc b w
  refine ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, ?_⟩
  intro lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have haobs (I : ℕ) : 1 ≤ A * diskEnergyGapRatio ^ I := by
    have hpow : 1 ≤ diskEnergyGapRatio ^ I :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    nlinarith
  have hraw := ht b w ν J hb hw hbw hν hform hJ A γ I₀ I₁ z₀ z₁
    hGW₀ hGW₁ hMix hγ (haobs I₀) ((hI₀ I₀).mpr le_rfl)
    (haobs I₁) ((hI₁ I₁).mpr le_rfl)
  have hint := capped_probability_product_bound pathLaw
    (sourceActualCount t b ν) (sourceActualCount t w ν) (sourceEarlyRootCap t ν)
    (sourceContinuationProbability t A γ b I₀ z₀ ν)
    (sourceContinuationProbability t A γ w I₁ z₁ ν)
    (K / (Real.exp t) ^ 4) (by positivity)
    (source_continuation_probability_nonneg t A γ b I₀ z₀ ν)
    (source_continuation_probability_nonneg t A γ w I₁ z₁ ν)
    (fun k l hk hl ↦ hprod ν k l hν hk hl)
  have he' : Real.exp (sourceDecouplingExponent D C₁ B W t ν J) ≤ Real.exp E :=
    Real.exp_le_exp.mpr (he ν J hν hgap.2.2)
  change _ ≤ Real.exp (sourceDecouplingExponent D C₁ B W t ν J) * _ at hraw
  calc
    _ ≤ _ := hraw
    _ ≤ Real.exp (sourceDecouplingExponent D C₁ B W t ν J) *
        (K / (Real.exp t) ^ 4) :=
      mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ ≤ Real.exp E * (K / (Real.exp t) ^ 4) :=
      mul_le_mul_of_nonneg_right he' (by positivity)
    _ = _ := by ring

end SRWTightness
