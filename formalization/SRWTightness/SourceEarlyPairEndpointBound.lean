import SRWTightness.SourceEarlyPairSuccessAbove
import SRWTightness.SourceEarlyOriginalRootRealMoment

open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.24 for the original complete pair events, with one common fixed gap threshold. -/
theorem source_early_pair_endpoint_bound [MeasurableSpace (List WordMark)]
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
    (hIncrement : BesselThreeIncrementInput) :
    ∃ A C : ℝ, ∃ J₀ a₀ : ℕ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < C ∧
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
  obtain ⟨A, C₀, J₀, ap, hA, hC₀, hJ₀, hJmin, hap, hp⟩ :=
    source_early_pair_success_bound_above hExt hFlat hErase hR hP hH hM hT hExit hGW
      hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
      Cm (2 / 5) hMoment hIncrement (by norm_num) (by norm_num) Jmin
  obtain ⟨am, ham, hm⟩ := hm J₀ hJmin
  refine ⟨A, 36 * C₀ + B, J₀, ap + am, hA, by positivity, hJ₀, by omega, ?_⟩
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

end SRWTightness
