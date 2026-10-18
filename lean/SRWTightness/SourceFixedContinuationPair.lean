import SRWTightness.SourceContinuationPairRadiusBound
import SRWTightness.SourceContinuationNonnegative
import SRWTightness.SourceRootCapHeight
import SRWTightness.ContinuationPairProduct

open Filter MeasureTheory
namespace SRWTightness

/-- Fixed continuation levels give a uniform inverse fourth-power radius bound for every
capped pair of starting populations. -/
theorem source_continuation_pair_fixed_level_bound (hGW : GWBarrierUpperInput)
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
  obtain ⟨A, C, hA, hC, ht⟩ := source_continuation_pair_radius_upper_bound hGW
    hReconstruct hBE hGaussian hReflection hBridge hReverse hPositive hInitial hHit
    Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨A, C, hA, hC, ?_⟩
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

end SRWTightness
