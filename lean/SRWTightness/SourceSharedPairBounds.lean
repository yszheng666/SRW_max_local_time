import SRWTightness.SourceSharedTerminalBounds
import SRWTightness.SourceEarlyPairsUniformSum
import SRWTightness.SourceFixedPairsUniformSum

open MeasureTheory Filter
open scoped BigOperators Topology
namespace SRWTightness

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_continuation_pair_fixed_level_bound_shared (hGW : GWBarrierUpperInput)
    (hReconstruct : BrownianBridgeReconstructionInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A γ) :
    ∃ C : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, ∃ I₀ I₁ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) ∧
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₁) ∧
      ∃ (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      (z₀ : Site) = b ∧ (z₁ : Site) = w ∧
      ∀ ν k l : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      sourceContinuationProbability t A γ b I₀ z₀ ν k *
        sourceContinuationProbability t A γ w I₁ z₁ ν l ≤
      (C * ((ν : ℝ) + 1) ^ 3 * Real.exp (16 * ((ν : ℝ) + 1))) /
        (Real.exp t) ^ 4 := by
  obtain ⟨C, hA, hC, ht⟩ := source_continuation_pair_radius_upper_bound_shared hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf Jmargin A hTerminal
  refine ⟨C, hA, hC, ?_⟩
  filter_upwards [ht, source_early_root_cap_quadratic] with t ht hcap
  intro b w
  obtain ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, hp⟩ := ht b w
  refine ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, ?_⟩
  intro ν k l hν hk hl
  have hheight : ∀ k : ℕ, k ≤ sourceEarlyRootCap t ν →
      Real.sqrt (2 * (k : ℝ)) ≤ 4 * ((ν : ℝ) + 1) := by
    intro k hk
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hh := (Nat.cast_le.mpr hk).trans (hcap ν)
    nlinarith only [hh]
  have he : Real.exp (2 * Real.sqrt (2 * (k : ℝ)) + 2 * Real.sqrt (2 * (l : ℝ))) ≤
      Real.exp (16 * ((ν : ℝ) + 1)) := by
    apply Real.exp_le_exp.mpr
    linarith only [hheight k hk, hheight l hl]
  have hn : Real.exp (-4 * (ν : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [show (0 : ℝ) ≤ ν from Nat.cast_nonneg _])
  calc
    _ ≤ _ := hp ν k l hν hk hl
    _ ≤ C * ((ν : ℝ) + 1) ^ 3 / (Real.exp t) ^ 4 * 1 *
        Real.exp (16 * ((ν : ℝ) + 1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hn (by positivity)) he
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_fixed_pair_success_bound_shared (hExt : ExteriorBridgeFactorizationInput)
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
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A γ) :
    diskPointGaussianMinimumRadius ≤ A ∧ ∀ a₀ : ℕ,
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
  obtain ⟨C₀, hA, hC₀, hcont⟩ := source_continuation_pair_fixed_level_bound_shared hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf Jmargin A hTerminal
  refine ⟨hA, ?_⟩
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

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_fixed_centered_pair_bound_shared (hExt : ExteriorBridgeFactorizationInput)
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
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A γ) :
    diskPointGaussianMinimumRadius ≤ A ∧ ∀ a₀ : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∃ ν : ℕ, ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) ≤ a₀ →
      ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      sourceEnlargedLaw.real
        (sourceCenteredSuccessEvent t A γ b I ∩ sourceCenteredSuccessEvent t A γ w I) ≤
      C / (Real.exp t) ^ 4 := by
  obtain ⟨hA, hp⟩ := source_fixed_pair_success_bound_shared hExt hFlat hR hP hH hM hT
    hGW hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf Jmargin A hTerminal
  refine ⟨hA, ?_⟩
  intro a₀
  obtain ⟨C, hC, ν, hp⟩ := hp a₀
  refine ⟨C, hC, ν, ?_⟩
  filter_upwards [hp] with t hp
  intro b w hb hw hbw ha I hI
  obtain ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, hpair⟩ := hp b w hb hw hbw ha
  have h0 := source_observation_level_unique t A I₀ I hI₀ hI
  have h1 := source_observation_level_unique t A I₁ I hI₁ hI
  subst I₀
  subst I₁
  intro lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
  rw [source_centered_success_event_eq t A γ b I z₀ hz₀,
    source_centered_success_event_eq t A γ w I z₁ hz₁]
  exact hpair hGW₀ hGW₁ hMix

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_fixed_pairs_uniform_sum_shared (hAnnulus : LatticeAnnulusCountInput)
    (hExt : ExteriorBridgeFactorizationInput)
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
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A γ) :
    diskPointGaussianMinimumRadius ≤ A ∧ ∀ a₀ : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [∀ b : Site, MeasurableSpace
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSingletonClass
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hForest : ∀ b : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        MarkedGWForestJointInput
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix : ∀ (b w : Site) (ν : ℕ), b ∈ sourceCandidateAnnulus (Real.exp t) →
        w ∈ sourceCandidateAnnulus (Real.exp t) → b ≠ w →
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      (∑ p ∈ sourceFixedDistancePairs t a₀, sourceEnlargedLaw.real
        (sourceCenteredSuccessEvent t A γ p.1 I ∩ sourceCenteredSuccessEvent t A γ p.2 I)) ≤
        C := by
  obtain ⟨hA, hp⟩ := source_fixed_centered_pair_bound_shared hExt hFlat hR hP hH hM hT
    hGW hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf Jmargin A hTerminal
  obtain ⟨c, N, hc, hN, hcount⟩ := hAnnulus
  refine ⟨hA, ?_⟩
  intro a₀
  obtain ⟨C, hC, ν, hp⟩ := hp a₀
  refine ⟨N ^ 2 * C, mul_pos (pow_pos hN 2) hC, ?_⟩
  filter_upwards [hp, Real.tendsto_exp_atTop.eventually hcount] with t hp hn
  intro I hI lm ls rm rs fm fs hForest hMix
  exact source_fixed_pair_sum_bound t A γ C N I a₀ hC.le hN.le hn.2
    (fun b w hb hw hbw ha ↦
      hp b w hb hw hbw ha I hI (hForest b hb) (hForest w hw) (hMix b w ν hb hw hbw))

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_early_pair_success_bound_above_shared (hExt : ExteriorBridgeFactorizationInput)
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
    (Jrequired : ℕ)
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A γ) :
    ∃ C : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
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
  obtain ⟨C₀, hA, hC₀, hcont⟩ := source_continuation_pair_radius_upper_bound_shared hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf Jmargin A hTerminal
  refine ⟨Real.exp (576 * D + 1) * C₀, J₀, aE + aP + aL, hA,
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

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_early_pair_endpoint_bound_shared [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
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
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A (2 / 5)) :
    ∃ C : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      3 ≤ J₀ ∧ 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let q := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
      ∃ I₀ I₁ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) ∧
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₁) ∧
      ∃ (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      (z₀ : Site) = b ∧ (z₁ : Site) = w ∧ ∀
      [MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
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
        (sourceSiteSuccessEvent t A (2 / 5) b I₀ z₀ ∩ sourceSiteSuccessEvent t A (2 / 5) w I₁ z₁) ≤
      C * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 / (Real.exp t) ^ 4 *
        Real.exp (-4 * ν - q ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * q + C * ((J : ℝ) + 1)) := by
  obtain ⟨B, hB, Jmin, hm⟩ :=
    source_early_original_root_real_moment hLast hrec hP hMarginal hJoint hFlat
  obtain ⟨C₀, J₀, ap, hA, hC₀, hJ₀, hJmin, hap, hp⟩ :=
    source_early_pair_success_bound_above_shared hExt hFlat hErase hR hP hH hM hT hExit hGW
      hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
      Cm (2 / 5) hMoment hIncrement (by norm_num) (by norm_num) Jmin Jmargin A hTerminal
  obtain ⟨am, ham, hm⟩ := hm J₀ hJmin
  refine ⟨36 * C₀ + B, J₀, ap + am, hA, by positivity, hJ₀, by omega, ?_⟩
  filter_upwards [hp, hm] with t hp hm
  intro b w hb hw hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let q := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
  obtain ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, hpair⟩ :=
    hp b w hb hw hbw (show ap ≤ _ by omega) hrange
  refine ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, ?_⟩
  intro cm cs clm cls lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
  have hann : ∀ x ∈ ({b, w} : Finset Site),
      Real.exp t / 4 ≤ Real.sqrt (normSq x) ∧ Real.sqrt (normSq x) ≤ Real.exp t / 3 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_sourceCandidateAnnulus _ (Real.exp_pos _) _).mp hb
    · exact (mem_sourceCandidateAnnulus _ (Real.exp_pos _) _).mp hw
  have hmoment := hm b w hbw (show am ≤ _ by omega) hrange hann
  have hraw := hpair hGW₀ hGW₁ hMix
  have hh := hraw.trans (mul_le_mul_of_nonneg_left hmoment (by positivity))
  have hcoef : 36 * C₀ ≤ 36 * C₀ + B := le_add_of_nonneg_right hB
  have hexp : B * ((J : ℝ) + 1) ≤ (36 * C₀ + B) * ((J : ℝ) + 1) := by
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc
    _ ≤ _ := hh
    _ = (36 * C₀) * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 / (Real.exp t) ^ 4 *
        Real.exp (-4 * ν - q ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * q + B * ((J : ℝ) + 1)) := by
      simp only [Real.exp_add, Real.exp_sub]
      ring
    _ ≤ _ := mul_le_mul
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity))
          (by positivity)) (by positivity))
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_early_centered_pair_endpoint_bound_shared [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
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
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A (2 / 5)) :
    ∃ C : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      3 ≤ J₀ ∧ 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let q := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
      ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      sourceEnlargedLaw.real
        (sourceCenteredSuccessEvent t A (2 / 5) b I ∩ sourceCenteredSuccessEvent t A (2 / 5) w I) ≤
      C * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 / (Real.exp t) ^ 4 *
        Real.exp (-4 * ν - q ^ 2 / (2 * ((j : ℝ) + 1)) + 4 * q + C * ((J : ℝ) + 1)) := by
  obtain ⟨C, J₀, a₀, hA, hC, hJ₀, ha₀, hp⟩ :=
    source_early_pair_endpoint_bound_shared hLast hrec hMarginal hJoint hExt hFlat hErase hR hP
      hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive
      hInitial hHit Cm hMoment hIncrement Jmargin A hTerminal
  refine ⟨C, J₀, a₀, hA, hC, hJ₀, ha₀, ?_⟩
  filter_upwards [hp] with t hp
  intro b w hb hw hbw ha hrange
  dsimp only
  intro I hI
  obtain ⟨I₀, I₁, hI₀, hI₁, z₀, z₁, hz₀, hz₁, hpair⟩ := hp b w hb hw hbw ha hrange
  have h0 := source_observation_level_unique t A I₀ I hI₀ hI
  have h1 := source_observation_level_unique t A I₁ I hI₁ hI
  subst I₀
  subst I₁
  intro cm cs clm cls lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
  rw [source_centered_success_event_eq t A (2 / 5) b I z₀ hz₀,
    source_centered_success_event_eq t A (2 / 5) w I z₁ hz₁]
  exact hpair hGW₀ hGW₁ hMix

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_early_pair_shell_decay_shared [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
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
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A (2 / 5)) :
    ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧
      3 ≤ J₀ ∧ 2 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ a : ℕ, a₀ ≤ a →
      a < sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
      [∀ b : Site, MeasurableSpace
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSingletonClass
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSpace
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ b : Site, MeasurableSingletonClass
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ b : Site, MeasurableSpace (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [∀ b : Site, MeasurableSingletonClass (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hForest : ∀ b : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        MarkedGWForestJointInput
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix : ∀ b w : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        w ∈ sourceCandidateAnnulus (Real.exp t) → b ≠ w →
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      sourcePairShellMass t A (2 / 5) I a ≤ Real.exp (-(a : ℝ) ^ (2 / 5 : ℝ) / 2) := by
  classical
  obtain ⟨C, J₀, ap, hA, hC, hJ₀, hap, hp⟩ :=
    source_early_centered_pair_endpoint_bound_shared hLast hrec hMarginal hJoint hExt hFlat hErase
      hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection hBridge hReverse
      hPositive hInitial hHit Cm hMoment hIncrement Jmargin A hTerminal
  obtain ⟨as, has, hs⟩ := source_early_pair_shell_of_endpoint hDisk hAnnulus C hC J₀
  refine ⟨J₀, max ap as, hA, hJ₀, has.trans (le_max_right _ _), ?_⟩
  filter_upwards [hp, hs] with t hp hs
  intro a ha hrange
  dsimp only
  intro I hI cm cs clm cls lm ls rm rs fm fs hForest hMix
  apply hs A I a ((le_max_right _ _).trans ha) hrange
  intro p hpairs
  obtain ⟨hZ, hne, hindex⟩ := Finset.mem_filter.mp hpairs
  obtain ⟨hb, hw⟩ := Finset.mem_product.mp hZ
  have hpair := hp p.1 p.2 hb hw hne
  rw [← hindex] at hpair
  exact hpair ((le_max_left _ _).trans ha) hrange I hI
    (hForest p.1 hb) (hForest p.2 hw) (hMix p.1 p.2 hb hw hne)

/-- The pair estimate uses the same internally supplied terminal radius as the one-point bound. -/
theorem source_early_pairs_uniform_sum_shared [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) (hExt : ExteriorBridgeFactorizationInput)
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
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (Jmargin A : ℝ) (hTerminal : SourceTerminalEstimate Jmargin A (2 / 5)) :
    ∃ C : ℝ, ∃ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
      2 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) → ∀
      [∀ j : ℕ, MeasurableSpace (FiniteExcursionRecord WordMark j)]
      [∀ j : ℕ, MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
      [∀ j : ℕ, MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
      [∀ j : ℕ, MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))]
      [∀ b : Site, MeasurableSpace
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ b : Site, MeasurableSingletonClass
        (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)]
      [∀ (b : Site) (ν : ℕ), MeasurableSpace (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      [∀ (b : Site) (ν : ℕ), MeasurableSingletonClass (List
        (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν))]
      (hForest : ∀ b : Site, b ∈ sourceCandidateAnnulus (Real.exp t) →
        MarkedGWForestJointInput
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))))
      (hMix : ∀ (b w : Site) (ν : ℕ), b ∈ sourceCandidateAnnulus (Real.exp t) →
        w ∈ sourceCandidateAnnulus (Real.exp t) → b ≠ w →
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I))) ν)),
      (∑ a ∈ Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t),
        sourcePairShellMass t A (2 / 5) I a) ≤ C := by
  classical
  obtain ⟨J₀, a₀, hA, hJ₀, ha₀, hp⟩ :=
    source_early_pair_shell_decay_shared hDisk hAnnulus hLast hrec hMarginal hJoint hExt hFlat
      hErase
      hR hP hH hM hT hExit hGW hReconstruct hBE hGaussian hReflection hBridge hReverse
      hPositive hInitial hHit Cm hMoment hIncrement Jmargin A hTerminal
  have hsum : Summable (fun n : ℕ ↦ Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2)) := by
    convert stretched_exponential_summable (1 / 2) (2 / 5) (by norm_num) (by norm_num) using 1
    funext n
    congr 1
    ring
  let C := (∑' n : ℕ, Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2)) + 1
  have hC : 0 < C := by
    have hh : 0 ≤ ∑' n : ℕ, Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2) :=
      tsum_nonneg (fun n : ℕ ↦ (Real.exp_pos (-(n : ℝ) ^ (2 / 5 : ℝ) / 2)).le)
    dsimp only [C]
    linarith only [hh]
  refine ⟨C, a₀, hA, hC, ha₀, ?_⟩
  filter_upwards [hp] with t hp
  intro I hI cm cs clm cls lm ls rm rs fm fs hForest hMix
  calc
    _ ≤ ∑ a ∈ Finset.Ico a₀ (sourceCoarseLowerLevel t + sourceCommonPairGap t),
        Real.exp (-(a : ℝ) ^ (2 / 5 : ℝ) / 2) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨ha0, har⟩ := Finset.mem_Ico.mp ha
      exact hp a ha0 har I hI hForest
        (fun b w hb hw hne ↦ hMix b w (a + sourceEarlyDistanceGap a J₀ + 5) hb hw hne)
    _ ≤ ∑' n : ℕ, Real.exp (-(n : ℝ) ^ (2 / 5 : ℝ) / 2) :=
      hsum.sum_le_tsum _ (fun n hn ↦ (Real.exp_pos _).le)
    _ ≤ C := le_add_of_nonneg_right (by norm_num)

end SRWTightness
