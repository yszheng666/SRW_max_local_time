import SRWTightness.SourceCompleteUncappedRootBound
import SRWTightness.SourceEarlyPrefixExterior
import SRWTightness.SourceEarlyDecouplingError
import SRWTightness.SourceContinuationPairRadiusBound

open MeasureTheory Filter
namespace SRWTightness

/-- The original early pair bound with an arbitrarily prescribed lower gap threshold. -/
theorem source_early_pair_success_bound_above (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) (hErase : ExteriorNestedCountInvarianceInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) (hExit : FiniteKilledWalkMomentInput)
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
    (Jrequired : ℕ) :
    ∃ A C : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      3 ≤ J₀ ∧ Jrequired ≤ J₀ ∧ 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
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
      C * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * Real.exp (-4 * ν) *
        ∫ ω, (sourceEarlyPrefixEvent t b j).indicator (fun u ↦ Real.exp
          (2 * Real.sqrt (2 * (sourceActualCount t b ν u : ℝ)) +
            2 * Real.sqrt (2 * (sourceActualCount t w ν u : ℝ)))) ω ∂pathLaw := by
  obtain ⟨D, C₁, B, W, Jbar, hD, hC₁, hB, hW, hJbar, hbound⟩ :=
    source_complete_uncapped_root_bound hExt hFlat hR hP hH hM hT hExit
  let J₀ : ℕ := max 3 (max ⌈Jbar⌉₊ Jrequired)
  have hJ₀ : 3 ≤ J₀ := le_max_left _ _
  have hJbar₀ : Jbar ≤ (J₀ : ℝ) :=
    (Nat.le_ceil Jbar).trans (Nat.cast_le.mpr ((le_max_left _ _).trans (le_max_right _ _)))
  obtain ⟨aE, haE, herror⟩ :=
    source_early_decoupling_exponent_bounded D C₁ B W hD.le hC₁.le J₀
  obtain ⟨aP, hprefix⟩ := source_early_prefix_exterior hErase J₀ hJ₀
  obtain ⟨aL, hlevels⟩ := source_early_distance_levels J₀
  obtain ⟨A, C₀, hA, hC₀, hcont⟩ := source_continuation_pair_radius_upper_bound hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, Real.exp (576 * D + 1) * C₀, J₀, aE + aP + aL, hA,
    mul_pos (Real.exp_pos _) hC₀, hJ₀,
    (le_max_right _ _).trans (le_max_right _ _), by omega, ?_⟩
  filter_upwards [hbound, herror, hprefix, hlevels, hcont] with t ht he hp hl hc
  intro b w hb hw hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  have haE' : aE ≤ a := by omega
  have haP : aP ≤ a := by omega
  have haL : aL ≤ a := by omega
  have ha1 : 1 ≤ a := haE.trans haE'
  have hν : ν ≤ 2 * sourceCoarseLowerLevel t := (hl a haL hrange).2.2
  have hj : j ≤ ν := by dsimp [j, ν]; omega
  have hJ : Jbar ≤ (J : ℝ) := hJbar₀.trans (Nat.cast_le.mpr
    (show J₀ ≤ J by dsimp [J, sourceEarlyDistanceGap]; omega))
  obtain ⟨G, hG⟩ := (hp b w hb hw hbw haP hrange).1
  obtain ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, hprod⟩ := hc b w
  refine ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, ?_⟩
  intro lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
  have hA4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have haobs (I : ℕ) : 1 ≤ A * diskEnergyGapRatio ^ I := by
    have hpow : 1 ≤ diskEnergyGapRatio ^ I :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    nlinarith
  have hraw := ht b w ν J hb hw hbw ha1 hν rfl hJ A γ I₀ I₁ z₀ z₁
    hGW₀ hGW₁ hMix hγ (haobs I₀) ((hI₀ I₀).mpr le_rfl)
    (haobs I₁) ((hI₁ I₁).mpr le_rfl) j G hj hG C₀ hC₀.le
    (fun k l hk hl ↦ hprod ν k l hν hk hl)
  have he' := Real.exp_le_exp.mpr (he a haE' hrange)
  have hmoment : 0 ≤ ∫ ω, (sourceEarlyPrefixEvent t b j).indicator (fun u ↦ Real.exp
      (2 * Real.sqrt (2 * (sourceActualCount t b ν u : ℝ)) +
        2 * Real.sqrt (2 * (sourceActualCount t w ν u : ℝ)))) ω ∂pathLaw := by
    apply integral_nonneg
    intro ω
    exact Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) ω
  refine hraw.trans ((mul_le_mul_of_nonneg_right he' (by positivity)).trans_eq ?_)
  ring

end SRWTightness
